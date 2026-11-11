module

public import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
public import DirectedDistances.KMSW.CommonFutureM0
public import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.KMSW.OutgoingIntervalFreshLeft

/-! # Rightmost paths and common strict-record futures in the one-sided KMSW map

Despite the file name, these results are stated under the one-sided UIQBOT
hypotheses (`L ≥ 0`, `L → ∞`, `R` unbounded below); they do NOT prove
coalescence of rightmost paths in `M_{0,∞}` (`lem-uibot-bdy`): the meeting of
two rightmost paths is not shown here;
`kmswRightmostPath_coalesces_of_common_vertex` only says two rightmost paths
agree after a common vertex.

The existing outgoing enumeration is ordered from left to right, so its last
edge is rightmost. -/

public section
namespace DirectedDistances.KMSW

open Filter Quiver MeasureTheory

/-- Under the one-sided no-sink hypotheses, the outgoing order at every
allocated vertex is nonempty (`lem-uibot-bdy`, -/
theorem kmswOutgoingEdgesLeftToRight_ne_nil
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv ≠ [] := by
  obtain ⟨e, he, hw⟩ := uibot_allocated_vertex_outgoing w hR v hv
  have hm := (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv e).2 ⟨he, hw⟩
  intro hnil
  simp [hnil] at hm

/-- The rightmost present outgoing edge at an allocated vertex, obtained as
the last entry of the exhaustive left-to-right outgoing order -/
@[expose] noncomputable def kmswRightmostOutgoingEdge
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v : ℕ) : ℕ :=
  (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v (halloc v)).getLast
    (kmswOutgoingEdgesLeftToRight_ne_nil w hfin hL htrans hR v (halloc v))

/-- The selected rightmost edge is present and leaves the specified vertex -/
theorem kmswRightmostOutgoingEdge_spec
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v : ℕ) :
    EdgePresent w (kmswRightmostOutgoingEdge w hfin hL htrans hR halloc v) ∧
      edgeWest w (kmswRightmostOutgoingEdge w hfin hL htrans hR halloc v) = v := by
  let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v (halloc v)
  have hmem : es.getLast (kmswOutgoingEdgesLeftToRight_ne_nil w hfin hL htrans hR v
      (halloc v)) ∈ es := List.getLast_mem _
  exact (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v (halloc v) _).1 hmem

/-- At the source, the selected rightmost edge is the root of the right -/
theorem kmswRightmostOutgoingEdge_source
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex) :
    kmswRightmostOutgoingEdge w hfin hL htrans hR halloc 0 =
      kmswRightBoundaryEdge w 0 := by
  classical
  let es := (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose
  have hsource : es.head? = some (kmswRightBoundaryEdge w 0) :=
    (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.2.1
  have hne : es ≠ [] := by
    intro he
    rw [he] at hsource
    simp at hsource
  have hhead : es.head hne = kmswRightBoundaryEdge w 0 := by
    exact (List.head_eq_iff_head?_eq_some hne).2 hsource
  have hrev : es.reverse ≠ [] := by simpa using hne
  change (es.reverse).getLast _ = _
  rw [List.getLast_reverse hrev]
  exact hhead

/-- The vertex sequence obtained by repeatedly following the rightmost
outgoing edge. Every vertex ID is allocated under the finite-incidence -/
@[expose] noncomputable def kmswRightmostNext
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) : ℕ :=
  edgeEast w (kmswRightmostOutgoingEdge w hfin hL htrans hR
    (kmsw_vertex_allocated_of_finite_incidence w hfin) v)

@[expose] noncomputable def kmswRightmostOrbit
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) : ℕ → ℕ
  | 0 => v
  | i + 1 => kmswRightmostNext w hfin hL htrans hR
      (kmswRightmostOrbit w hfin hL htrans hR v i)

/-- The `i`th edge selected along the rightmost orbit. -/
@[expose] noncomputable def kmswRightmostOrbitEdge
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v i : ℕ) : ℕ :=
  kmswRightmostOutgoingEdge w hfin hL htrans hR
    (kmsw_vertex_allocated_of_finite_incidence w hfin)
    (kmswRightmostOrbit w hfin hL htrans hR v i)

/-- Every successive edge of the rightmost orbit is a present arrow with the
specified consecutive endpoints (`def-infinite-geo`, -/
theorem kmswRightmostOrbitEdge_spec
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v i : ℕ) :
    EdgePresent w (kmswRightmostOrbitEdge w hfin hL htrans hR v i) ∧
      edgeWest w (kmswRightmostOrbitEdge w hfin hL htrans hR v i) =
        kmswRightmostOrbit w hfin hL htrans hR v i ∧
      edgeEast w (kmswRightmostOrbitEdge w hfin hL htrans hR v i) =
        kmswRightmostOrbit w hfin hL htrans hR v (i + 1) := by
  have h := kmswRightmostOutgoingEdge_spec w hfin hL htrans hR
    (kmsw_vertex_allocated_of_finite_incidence w hfin)
    (kmswRightmostOrbit w hfin hL htrans hR v i)
  exact ⟨h.1, h.2, rfl⟩

/-- The finite directed path consisting of the first `n` rightmost edges. -/
@[expose] noncomputable def kmswRightmostPathPrefix
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) :
    (n : ℕ) → Path (⟨v⟩ : PresentVertex w)
      ⟨kmswRightmostOrbit w hfin hL htrans hR v n⟩
  | 0 => Path.nil
  | n + 1 =>
    let e := kmswRightmostOrbitEdge w hfin hL htrans hR v n
    let he := kmswRightmostOrbitEdge_spec w hfin hL htrans hR v n
    (kmswRightmostPathPrefix w hfin hL htrans hR v n).cons
      ⟨e, he.1, by simpa [e, kmswRightmostOrbitEdge] using he.2.1,
        by simpa [e, kmswRightmostOrbitEdge] using he.2.2⟩

/-- The prefix has exactly its prescribed number of directed edges. -/
theorem kmswRightmostPathPrefix_length
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v n : ℕ) :
    (kmswRightmostPathPrefix w hfin hL htrans hR v n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [kmswRightmostPathPrefix, ih]

/-- The traversal edge list of a prefix is precisely the selected rightmost -/
theorem kmswRightmostPathPrefix_edges
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v n : ℕ) :
    pathEdgeList (kmswRightmostPathPrefix w hfin hL htrans hR v n) =
      List.ofFn (fun i : Fin n => kmswRightmostOrbitEdge w hfin hL htrans hR v i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [kmswRightmostPathPrefix, pathEdgeList]
    rw [ih, List.ofFn_succ_last]
    simp

/-- The infinite directed path that always takes the rightmost outgoing edge -/
@[expose] noncomputable def kmswRightmostPath
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) :
    InfinitePresentPath w ⟨v⟩ where
  edge := kmswRightmostOrbitEdge w hfin hL htrans hR v
  initial N :=
    ⟨⟨kmswRightmostOrbit w hfin hL htrans hR v N⟩,
      kmswRightmostPathPrefix w hfin hL htrans hR v N⟩
  prefix_length N := kmswRightmostPathPrefix_length w hfin hL htrans hR v N
  prefix_edges N := kmswRightmostPathPrefix_edges w hfin hL htrans hR v N

/-- Each edge of the infinite path is the selected rightmost outgoing edge -/
theorem kmswRightmostPath_edge_spec
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v i : ℕ) :
    EdgePresent w ((kmswRightmostPath w hfin hL htrans hR v).edge i) ∧
      edgeWest w ((kmswRightmostPath w hfin hL htrans hR v).edge i) =
        kmswRightmostOrbit w hfin hL htrans hR v i ∧
      edgeEast w ((kmswRightmostPath w hfin hL htrans hR v).edge i) =
        kmswRightmostOrbit w hfin hL htrans hR v (i + 1) := by
  exact kmswRightmostOrbitEdge_spec w hfin hL htrans hR v i

/-- Once two deterministic rightmost paths visit the same vertex, their
successive vertices agree forever (`lem-uibot-bdy`, -/
theorem kmswRightmostOrbit_tail_eq
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (x y i j : ℕ)
    (hxy : kmswRightmostOrbit w hfin hL htrans hR x i =
      kmswRightmostOrbit w hfin hL htrans hR y j) :
    ∀ t, kmswRightmostOrbit w hfin hL htrans hR x (i + t) =
      kmswRightmostOrbit w hfin hL htrans hR y (j + t) := by
  intro t
  induction t with
  | zero => simpa using hxy
  | succ t ih =>
    rw [Nat.add_succ, Nat.add_succ, kmswRightmostOrbit, kmswRightmostOrbit, ih]

/-- In the source path notation, a shared vertex forces all later vertices of
the two rightmost paths to agree (`lem-uibot-bdy`, -/
theorem kmswRightmostPath_coalesces_of_common_vertex
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (x y i j : ℕ)
    (hxy : ((kmswRightmostPath w hfin hL htrans hR x).initial i).1.id =
      ((kmswRightmostPath w hfin hL htrans hR y).initial j).1.id) :
    ∀ t, ((kmswRightmostPath w hfin hL htrans hR x).initial (i + t)).1.id =
      ((kmswRightmostPath w hfin hL htrans hR y).initial (j + t)).1.id := by
  have hxy' : kmswRightmostOrbit w hfin hL htrans hR x i =
      kmswRightmostOrbit w hfin hL htrans hR y j := by
    simpa [kmswRightmostPath] using hxy
  intro t
  simpa [kmswRightmostPath] using
    kmswRightmostOrbit_tail_eq w hfin hL htrans hR x y i j hxy' t

/-- The source's rightmost edge remains its same edge at every finite stage -/
theorem kmswRightmostOutgoingEdge_source_stage
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex) (n : ℕ) :
    kmswRightmostOutgoingEdge w hfin hL htrans hR halloc 0 <
        (kmswStage w n).nextEdge ∧
      (kmswStage w n).present
        (kmswRightmostOutgoingEdge w hfin hL htrans hR halloc 0) = true := by
  rw [kmswRightmostOutgoingEdge_source w hfin hL htrans hR halloc,
    kmswRightBoundaryEdge_zero]
  have h := present_mono w (n := 0) (e := 0) (by simp [kmswStage, kmswInit])
      (by simp [kmswStage, kmswInit]) n (Nat.zero_le n)
  exact h

/-- Almost surely, for the Pitman code `w` built from the i.i.d. sequence `ω`
under `RandomWalk.iidCodeMeasure` (not i.i.d. `M_{0,∞}` codes), the UIQBOT
hypotheses hold and the rightmost infinite path from every vertex is defined
asserted. -/
theorem iidCodes_ae_rightmostPath_exists :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (htrans : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
        (hL : ∀ j, 0 ≤ L w j),
        ∀ v : ℕ, ∃ P : InfinitePresentPath w ⟨v⟩,
          P = kmswRightmostPath w hfin hL htrans hR v := by
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices] with ω hω
  obtain ⟨hfin, htrans, hR, hL, _⟩ := hω
  exact ⟨hfin, htrans, hR, hL, fun v => ⟨kmswRightmostPath _ hfin hL htrans hR v, rfl⟩⟩

end DirectedDistances.KMSW
