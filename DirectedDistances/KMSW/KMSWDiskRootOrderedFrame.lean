module

public import DirectedDistances.KMSW.KMSWDiskRootedLaw
public import DirectedDistances.KMSW.KMSWStageFrontierChain

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The lower-left boundary vertices in the west-to-east order of `State.LL`.
For a nonempty LL list this is the west endpoint of its first edge followed by
the east endpoints of its edges. This is geometric bookkeeping; missing edges
remain unoriented. Helper toward Proposition 5.16 -/
@[expose] def llVertices (S : State) : List ℕ :=
  (S.LL.head?.map S.west).toList ++ S.LL.map S.east

/-- The LL vertex chain has one more entry than its nonempty edge list.
662–676, 835`), not the paper result. -/
theorem llVertices_length (S : State) (hne : S.LL ≠ []) :
    (llVertices S).length = S.LL.length + 1 := by
  unfold llVertices
  rw [List.head?_eq_some_head hne]
  simp

/-- Each finite stage LL edge joins the adjacent vertices in `llVertices`.
The LL list is west-to-east: `east(edgeᵢ) = west(edgeᵢ₊₁)`. The edge can be
missing and this statement does not orient it. Helper toward Proposition 5.16
No ball, Definition 3.8 extension, or infinite UIBHBOT carrier is treated. -/
theorem kmswStage_llVertices_edge_endpoints (u : ℕ → Fin 3) (n i : ℕ)
    (hi : i < (kmswStage u n).LL.length) :
    let S := kmswStage u n
    S.west (S.LL.get ⟨i, hi⟩) =
        (llVertices S)[i]'(by
          have hiS : i < S.LL.length := by simpa only [S] using hi
          have hne : S.LL ≠ [] := by
            intro h
            have hzero : S.LL.length = 0 := by simp [h]
            omega
          rw [llVertices_length S hne]
          omega) ∧
      S.east (S.LL.get ⟨i, hi⟩) =
        (llVertices S)[i + 1]'(by
          have hiS : i < S.LL.length := by simpa only [S] using hi
          have hne : S.LL ≠ [] := by
            intro h
            have hzero : S.LL.length = 0 := by simp [h]
            omega
          rw [llVertices_length S hne]
          omega) := by
  let S := kmswStage u n
  have hiS : i < S.LL.length := by simpa only [S] using hi
  have hne : S.LL ≠ [] := by
    intro h
    have hzero : S.LL.length = 0 := by simp [h]
    omega
  have hhead : S.LL.head? = some (S.LL.head hne) :=
    List.head?_eq_some_head hne
  have hchain := (kmswStageFrontierChain_all u n).LL_chain
  change List.IsChain (fun e f => S.east e = S.west f) S.LL at hchain
  rw [List.isChain_iff_getElem] at hchain
  constructor
  · by_cases hi0 : i = 0
    · subst i
      have hget : S.LL.get ⟨0, hiS⟩ = S.LL.head hne := by
        simp only [List.get_eq_getElem, List.head_eq_getElem]
      have hfirst : S.west (S.LL.get ⟨0, hiS⟩) =
          (llVertices S)[0]'(by rw [llVertices_length S hne]; omega) := by
        rw [hget]
        simp [llVertices, hhead]
      exact hfirst
    · have hprev : i - 1 + 1 = i := by omega
      have hrel := hchain (i - 1) (by omega : i - 1 + 1 < S.LL.length)
      have hbound : i < (llVertices S).length := by
        rw [llVertices_length S hne]
        omega
      have hvertex : (llVertices S)[i]'hbound =
          S.east (S.LL.get ⟨i - 1, by omega⟩) := by
        simp only [llVertices, hhead, Option.map_some, Option.toList_some]
        have hprefix : ([S.west (S.LL.head hne)] : List ℕ).length = 1 := by
          simp
        rw [List.getElem_append_right (by rw [hprefix]; omega)]
        simp only [List.getElem_map]
        congr 1
      have hrel' : S.east (S.LL.get ⟨i - 1, by omega⟩) =
          S.west (S.LL.get ⟨i, hi⟩) := by
        simpa only [List.get_eq_getElem, hprev] using hrel
      exact (hvertex.trans hrel').symm
  · have hbound : i + 1 < (llVertices S).length := by
      rw [llVertices_length S hne]
      omega
    have hvertex : (llVertices S)[i + 1]'hbound =
        S.east (S.LL.get ⟨i, hi⟩) := by
      simp only [llVertices, hhead, Option.map_some, Option.toList_some]
      rw [List.getElem_append_right (by simp)]
      simp only [List.getElem_map]
      congr 1
    exact hvertex.symm

/-- The disk's selected missing edge is in west-to-east LL position
`LL.length - 1 - k`; `k + 1` is its count from the sink side. The LL list has
exactly `ℓ - 1` edges, all missing; the nonmissing sink-adjacent boundary edge
is accounted for outside this list. Missing edges remain unoriented. Helper
toward Proposition 5.16 -/
theorem kmswDiskRootEdge_ll_position {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let S := kmswStage u n
    let e := kmswLLCreatedEdge u (kmswDiskFirstHit c k)
    let p : Fin S.LL.length :=
      ⟨S.LL.length - 1 - k.val, by
        have h := (kmswDiskFiniteSample_index_bound c k).1
        have hk := k.isLt
        rw [h]
        omega⟩
    S.LL.length = ℓ - 1 ∧
      (∀ f ∈ S.LL, S.present f = false) ∧
      p.val + (k.val + 1) = S.LL.length ∧ S.LL.get p = e := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let S := kmswStage u n
  let e := kmswLLCreatedEdge u (kmswDiskFirstHit c k)
  let p : Fin S.LL.length :=
    ⟨S.LL.length - 1 - k.val, by
      have h := (kmswDiskFiniteSample_index_bound c k).1
      have hk := k.isLt
      rw [h]
      omega⟩
  have hindex := kmswDiskFiniteSample_index_bound c k
  have hreverse : S.LL.get p = S.LL.reverse.get
      ⟨k.val, by
        simp only [List.length_reverse]
        rw [hindex.1]
        exact k.isLt⟩ := by
    simp only [List.get_eq_getElem, List.getElem_reverse]
    rfl
  have hroot := (kmswDiskFirstHit_spec c k).2.2.2.2.2
  dsimp only [u, S, e] at hreverse hroot ⊢
  refine ⟨hindex.1, ?_, ?_, ?_⟩
  · intro f hf
    have hstatus := kmswStage_status u n
    have hb := (kmswStage_boundary_ids_lt_nextEdge u n).2 f (by
      simp only [List.mem_append]
      tauto)
    exact (hstatus.1 f hb).2 (Or.inr hf)
  · have hk := hindex.2
    have hkS : k.val + 1 ≤ S.LL.length := by simpa only [u, S] using hk
    have hp := p.isLt
    change S.LL.length - 1 - k.val < S.LL.length at hp
    change S.LL.length - 1 - k.val + (k.val + 1) = S.LL.length
    omega
  · exact hreverse.trans hroot

/-- Helper toward prop-disk-bs-conv / Proposition 5.16
`d := kmswDiskRootDart c k`, the source-ordered root `(x₀, x₁)` is
`(endpoint (edgeFlip d), endpoint d)`. Thus `stageEndpoint (edgeFlip d) = west e`
is `x₀` (the ball centre), and `stageEndpoint d = east e` is `x₁`. The LL list
is west-to-east; missing edges remain unoriented. No ball,
treated; not the paper result. -/
theorem kmswDiskRootDart_ordered_frame {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let S := kmswStage u n
    let e := kmswLLCreatedEdge u (kmswDiskFirstHit c k)
    let p : Fin S.LL.length :=
      ⟨S.LL.length - 1 - k.val, by
        have h := (kmswDiskFiniteSample_index_bound c k).1
        have hk := k.isLt
        rw [h]
        omega⟩
    stageEndpoint S (edgeFlip S.nextEdge (kmswDiskRootDart c k)) = S.west e ∧
      stageEndpoint S (kmswDiskRootDart c k) = S.east e ∧
      (llVertices S)[p.val]'(by
        have h := (kmswDiskFiniteSample_index_bound c k).1
        have hlen : S.LL.length = ℓ - 1 := by simpa only [S] using h
        have hk := k.isLt
        have hpos : 0 < S.LL.length := by rw [hlen]; omega
        have hne := List.ne_nil_of_length_pos hpos
        rw [llVertices_length S hne]
        omega) = S.west e ∧
      (llVertices S)[p.val + 1]'(by
        have h := (kmswDiskFiniteSample_index_bound c k).1
        have hp := p.isLt
        have hlen : S.LL.length = ℓ - 1 := by simpa only [S] using h
        have hpos : 0 < S.LL.length := by rw [hlen]; omega
        have hne := List.ne_nil_of_length_pos hpos
        rw [llVertices_length S hne]
        omega) = S.east e := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let S := kmswStage u n
  let e := kmswLLCreatedEdge u (kmswDiskFirstHit c k)
  let p : Fin S.LL.length :=
    ⟨S.LL.length - 1 - k.val, by
      have h := (kmswDiskFiniteSample_index_bound c k).1
      have hk := k.isLt
      rw [h]
      omega⟩
  have hposition := kmswDiskRootEdge_ll_position c k
  dsimp only [u, S, e, p] at hposition
  have hendpoint := kmswStage_llVertices_edge_endpoints u n p.val p.isLt
  dsimp only [u, S] at hendpoint
  have hselected : S.LL.get p = e := hposition.2.2.2
  have hselected' : S.LL[p.val] = e := by
    simpa only [List.get_eq_getElem] using hselected
  have hwest := hendpoint.1
  have heast := hendpoint.2
  simp only [List.get_eq_getElem] at hwest
  simp only [List.get_eq_getElem] at heast
  rw [hselected'] at hwest heast
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [stageEndpoint, edgeFlip, kmswDiskRootDart]
  · simp [stageEndpoint, kmswDiskRootDart]
  · exact hwest.symm
  · exact heast.symm

end DirectedDistances.KMSW
