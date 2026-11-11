module

public import DirectedDistances.PaperProofs.Section4.ThinMapGeometricCarrier
public import DirectedDistances.PaperProofs.Section4.ThinTruncationDecoder
import DirectedDistances.PaperProofs.Section4.ThinCutCompatibility
import DirectedDistances.KMSW.InfinitePresentPathCutVisit

/-! # Geometric ancestor truncation carriers

Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

The proved exhaustion below concerns the seam and the indexed exterior boundary only.
It does not identify a selected finite cut half with the geometric side. In particular,
no `sourceAncestorClass` is defined here: constructing it through
`finiteThinMapOfAncestors` still requires a finite half representative and a faithful
identification of its ancestor vertices, darts, rotations, faces and indexed markings.
The public `finiteThinMapOfAncestors_eq_iff` and
`halfTruncate_some_mk_eq_of_restriction_iso` now compare restrictions of differently
sized finite halves. They require an explicit marked restriction isomorphism; they do
not supply a finite representative of the geometric restriction or identify its
carriers with a selected cut half. Thus the obstruction is geometric representability
and ancestor confinement, rather than the availability of a restriction equality API.

For the standing data below, including the infinite cut-vertex property provided on the
coherent domain, the remaining interior exhaustion goals are exactly

```
∀ v ∈ sideVertices w hfin hL htrans hR P a,
  ∃ s, v ∈ sourceAncestorVertices w hfin hL htrans hR P a s
∀ e ∈ sideEdges w hfin hL htrans hR P a,
  ∃ s, e ∈ sourceAncestorEdges w hfin hL htrans hR P a s
```

In particular, the missing directed confinement statement is

```
∀ v ∈ sideVertices w hfin hL htrans hR P a,
  ∃ s, Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a)
    v (thinMapBoundaryVertex w hfin hL htrans hR a s)
```

Cut-vertex visitation is proved for paths in the whole present graph. It does not
assert that a path from an arbitrary geometric side vertex stays in that side.
No confinement premise or uncharacterized choice of a finite class is introduced here.

After a geometrically characterized `sourceAncestorClass` is constructed on the coherent
domain, the remaining one-cut identification has the following required statement
(with `x`, `T`, `hT` as in `thinTruncationAt`):

```
∀ (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
  (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
    (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
  halfTruncate a s (selectedCutSide x T a k q.1) =
    some (sourceAncestorClass x T hT a s q)
```

The assembly threshold remains `s + 1`; zero is the source and level `i + 1`
targets the head of boundary edge `i`. The manuscript's ordinal convention has not
been identified with this indexing by the present lemmas. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter Quiver

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
  (P : InfinitePresentPath w ⟨0⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
theorem sourceAncestorVertices_subset_sideVertices (a : ThinMapSide) (s : ℕ) :
    sourceAncestorVertices w hfin hL htrans hR P a s ⊆
      sideVertices w hfin hL htrans hR P a :=
  fun _ hv => hv.1

private theorem boundary_edge_mem (a : ThinMapSide) (i : ℕ) :
    (thinMapBoundaryDart w hfin hL htrans hR a i).1 ∈
      sideEdges w hfin hL htrans hR P a := by
  have hb : pathTrace (monotoneFamilyDrawing w hfin (monotone_family_all w))
      (thinMapBoundaryDart w hfin hL htrans hR a) ⊆
      thinMapSideRegion w hfin hL htrans hR P a := by
    cases a with
    | left => exact leftBoundaryTrace_subset_sideRegion w hfin hL htrans hR P
    | right => exact rightBoundaryTrace_subset_sideRegion w hfin hL htrans hR P
  have hd : (thinMapBoundaryDart w hfin hL htrans hR a i).2 = false := by
    cases a <;> rfl
  intro z hz
  apply hb
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  simpa only [← hd, Prod.mk.eta] using hz

private theorem boundary_edge_west (a : ThinMapSide) (i : ℕ) :
    edgeWest w (thinMapBoundaryDart w hfin hL htrans hR a i).1 =
      thinMapBoundaryVertex w hfin hL htrans hR a i := by
  cases a with
  | left =>
    cases i with
    | zero => exact (kmswLeftBoundary_infinite_present_path w htrans hL hR).2.2.1
    | succ i => exact ((kmswLeftBoundary_infinite_present_path w htrans hL hR).2.1 i).symm
  | right =>
    let B := kmswRightmostPath w hfin hL htrans hR 0
    cases i with
    | zero => exact B.first_edge_outgoing.2
    | succ i => exact (infinitePresentPath_edge_chain B i).symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Consecutive indexed boundary vertices are joined inside the side. -/
theorem thinMapBoundaryVertex_step (a : ThinMapSide) (i : ℕ) :
    sideDirectedStep w hfin hL htrans hR P a
      (thinMapBoundaryVertex w hfin hL htrans hR a i)
      (thinMapBoundaryVertex w hfin hL htrans hR a (i + 1)) := by
  refine ⟨(thinMapBoundaryDart w hfin hL htrans hR a i).1,
    boundary_edge_mem w hfin hL htrans hR P a i, ?_,
    boundary_edge_west w hfin hL htrans hR a i, rfl⟩
  cases a with
  | left => exact (kmswLeftBoundary_infinite_present_path w htrans hL hR).2.2.2 i
  | right => exact ((kmswRightmostPath w hfin hL htrans hR 0).edge_outgoing i).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Ancestor vertex carriers increase with the boundary index. -/
theorem sourceAncestorVertices_mono (a : ThinMapSide) :
    Monotone (sourceAncestorVertices w hfin hL htrans hR P a) := by
  intro s t hst v hv
  refine ⟨hv.1, ?_⟩
  induction t, hst using Nat.le_induction with
  | base => exact hv.2
  | succ t _ ih =>
    exact ih.tail (thinMapBoundaryVertex_step w hfin hL htrans hR P a t)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The indexed boundary vertex belongs to its own ancestor carrier. -/
theorem thinMapBoundaryVertex_mem_sourceAncestorVertices (a : ThinMapSide) (s : ℕ) :
    thinMapBoundaryVertex w hfin hL htrans hR a s ∈
      sourceAncestorVertices w hfin hL htrans hR P a s := by
  refine ⟨?_, .refl⟩
  cases s with
  | zero => exact source_mem_sideVertices w hfin hL htrans hR P a
  | succ i =>
    exact (sideEdges_endpoints w hfin hL htrans hR P a
      (boundary_edge_mem w hfin hL htrans hR P a i)).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
All geometric side edges whose endpoints are ancestors are retained, including missing edges. -/
@[expose] noncomputable def sourceAncestorEdges (a : ThinMapSide) (s : ℕ) : Set ℕ :=
  {e | e ∈ sideEdges w hfin hL htrans hR P a ∧
    edgeWest w e ∈ sourceAncestorVertices w hfin hL htrans hR P a s ∧
    edgeEast w e ∈ sourceAncestorVertices w hfin hL htrans hR P a s}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Ancestor edge carriers increase with the boundary index. -/
theorem sourceAncestorEdges_mono (a : ThinMapSide) :
    Monotone (sourceAncestorEdges w hfin hL htrans hR P a) := by
  intro s t hst e he
  exact ⟨he.1, sourceAncestorVertices_mono w hfin hL htrans hR P a hst he.2.1,
    sourceAncestorVertices_mono w hfin hL htrans hR P a hst he.2.2⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every ancestor edge carrier is finite, without imposing presence on its geometric edges. -/
theorem sourceAncestorEdges_finite (a : ThinMapSide) (s : ℕ) :
    (sourceAncestorEdges w hfin hL htrans hR P a s).Finite := by
  have hf := (sourceAncestorVertices_finite w hfin hL htrans hR P a s).biUnion
    (fun v _ => hfin v)
  apply hf.subset
  intro e he
  apply Set.mem_iUnion.mpr
  refine ⟨edgeWest w e, Set.mem_iUnion.mpr ⟨he.2.1, ?_⟩⟩
  have ha := kmsw_edge_allocated_by_self w e
  exact ⟨e, ha, Or.inl (edge_endpoints_eq w ha).1⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The boundary edge with index `i` is retained at level `i + 1`. -/
theorem thinMapBoundaryDart_mem_sourceAncestorEdges (a : ThinMapSide) (i : ℕ) :
    (thinMapBoundaryDart w hfin hL htrans hR a i).1 ∈
      sourceAncestorEdges w hfin hL htrans hR P a (i + 1) := by
  refine ⟨boundary_edge_mem w hfin hL htrans hR P a i, ?_, ?_⟩
  · rw [boundary_edge_west w hfin hL htrans hR a i]
    exact sourceAncestorVertices_mono w hfin hL htrans hR P a (Nat.le_succ i)
      (thinMapBoundaryVertex_mem_sourceAncestorVertices w hfin hL htrans hR P a i)
  · exact thinMapBoundaryVertex_mem_sourceAncestorVertices w hfin hL htrans hR P a (i + 1)

private theorem seam_step (a : ThinMapSide) (i : ℕ) :
    sideDirectedStep w hfin hL htrans hR P a
      (P.initial i).1.id (P.initial (i + 1)).1.id :=
  ⟨P.edge i, seamEdge_mem_sideEdges w hfin hL htrans hR P a i,
    (P.edge_outgoing_at_initial w i).1, (P.edge_outgoing_at_initial w i).2,
    (P.edge_incoming_at_succ w i).2⟩

include hL htrans hR in
private theorem cut_vertex_initial_index {v : ℕ} (hv : mapCutVertex w hfin v)
    (Q : InfinitePresentPath w ⟨0⟩) : ∃ j, (Q.initial j).1.id = v := by
  obtain ⟨j, hj | hj⟩ :=
    InfinitePresentPath.visits_mapCutVertex w hfin htrans hR hL hv Q
  · exact ⟨j, (Q.edge_outgoing_at_initial w j).2.symm.trans hj⟩
  · exact ⟨j + 1, (Q.edge_incoming_at_succ w j).2.symm.trans hj⟩

private theorem cut_vertex_boundary_index (a : ThinMapSide) {v : ℕ}
    (hv : mapCutVertex w hfin v) :
    ∃ s, thinMapBoundaryVertex w hfin hL htrans hR a s = v := by
  cases a with
  | left =>
    obtain ⟨e, hedge, hw | he⟩ := (mapLeftBoundaryVertex_iff w hfin htrans v).mp hv.1
    · obtain ⟨i, rfl⟩ := (isLeftBoundaryEdge_iff w htrans e).mp hedge
      exact ⟨i, (boundary_edge_west w hfin hL htrans hR .left i).symm.trans hw⟩
    · obtain ⟨i, rfl⟩ := (isLeftBoundaryEdge_iff w htrans e).mp hedge
      exact ⟨i + 1, he⟩
  | right =>
    let B := kmswRightmostPath w hfin hL htrans hR 0
    obtain ⟨j, hj⟩ := cut_vertex_initial_index w hfin hL htrans hR hv B
    refine ⟨j, ?_⟩
    exact (boundary_edge_west w hfin hL htrans hR .right j).symm.trans
      ((B.edge_outgoing_at_initial w j).2.trans hj)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Infinite map cut vertices imply that every seam vertex occurs at some ancestor level.
The cut infinitude is part of `selectedCutCoherentDomain_spec`. -/
theorem seamVertex_mem_sourceAncestorVertices_some
    (hcuts : {v : ℕ | mapCutVertex w hfin v}.Infinite) (a : ThinMapSide) (i : ℕ) :
    ∃ s, (P.initial i).1.id ∈ sourceAncestorVertices w hfin hL htrans hR P a s := by
  classical
  let early : Finset ℕ := (Finset.range i).image (fun j => (P.initial j).1.id)
  obtain ⟨v, hv, hvearly⟩ := hcuts.exists_notMem_finset early
  obtain ⟨j, hj⟩ := cut_vertex_initial_index w hfin hL htrans hR hv P
  have hij : i ≤ j := by
    by_contra hn
    apply hvearly
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), hj⟩
  obtain ⟨s, hs⟩ := cut_vertex_boundary_index w hfin hL htrans hR a hv
  refine ⟨s, seamVertex_mem_sideVertices w hfin hL htrans hR P a i, ?_⟩
  rw [hs, ← hj]
  clear hj
  induction j, hij using Nat.le_induction with
  | base => exact .refl
  | succ j _ ih => exact ih.tail (seam_step w hfin hL htrans hR P a j)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Infinite map cut vertices imply that every seam edge occurs at some ancestor level.
The same level retains both endpoints and the original geometric edge ID. -/
theorem seamEdge_mem_sourceAncestorEdges_some
    (hcuts : {v : ℕ | mapCutVertex w hfin v}.Infinite) (a : ThinMapSide) (i : ℕ) :
    ∃ s, P.edge i ∈ sourceAncestorEdges w hfin hL htrans hR P a s := by
  obtain ⟨s, hs⟩ :=
    seamVertex_mem_sourceAncestorVertices_some w hfin hL htrans hR P hcuts a (i + 1)
  refine ⟨s, seamEdge_mem_sideEdges w hfin hL htrans hR P a i, ?_, ?_⟩
  · rw [(P.edge_outgoing_at_initial w i).2]
    exact ⟨seamVertex_mem_sideVertices w hfin hL htrans hR P a i,
      hs.2.head (seam_step w hfin hL htrans hR P a i)⟩
  · rw [(P.edge_incoming_at_succ w i).2]
    exact hs

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The decoder follows from the explicit pairwise compatibility hypothesis below.
This is a sufficient route; the assembly's canonical least-good-cut comparison is -/
theorem thinTruncationAt_decode_of_halfTruncate_cut_eq
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, DirectedDistances.RandomWalk.IsPositiveSuccessTime
      (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (s : ℕ)
    (hcutcompat : ∀ (a' : ThinMapSide) (s' k K : ℕ)
      (q : selectedCutCoherentDomain x T hT),
      (s' : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
      (s' : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (K + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2) →
      halfTruncate a' s' (match a' with
        | .left => (selectedCutPastCuts x T (k + 1) q.1).1
        | .right => (selectedCutPastCuts x T (k + 1) q.1).2) =
      halfTruncate a' s' (match a' with
        | .left => (selectedCutPastCuts x T (K + 1) q.1).1
        | .right => (selectedCutPastCuts x T (K + 1) q.1).2))
    (k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
      (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    thinTruncationAt x T hT a s q =
      halfTruncate a s (selectedCutSide x T a k q.1) :=
  thinTruncationAt_decode_of_compat x T hT a s
    (fun k K q hk hK => hcutcompat a s k K q hk hK) k q hk

end DirectedDistances.PaperProofs.Section4
