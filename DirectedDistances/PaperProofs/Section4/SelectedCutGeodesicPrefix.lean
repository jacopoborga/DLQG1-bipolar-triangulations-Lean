module

public import DirectedDistances.PaperProofs.Section4.ThinCutCompatibility
public import DirectedDistances.PaperProofs.Section4.ThinCutSideCarrierCompatibility
public import DirectedDistances.KMSW.PastLeftmostPathInduction
import DirectedDistances.KMSW.StageInfiniteOutgoingOrderSource
import DirectedDistances.KMSW.PastTraceCutPath























public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Quiver

section PastCutTrace

variable (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ)
    (hcut : mapCutVertex w hfin (recordVertex w t).id)

include hcut

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At a map cut, the past LDP trace is a prefix of the infinite leftmost path. -/
theorem selectedCut_pastLdpTrace_eq_infinitePrefix
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

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At a map cut, the past SDP trace is a prefix of the infinite leftmost path. -/
theorem selectedCut_pastSdpTrace_eq_infinitePrefix
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

end PastCutTrace

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The finite edge lists of two initial segments of one infinite path are ordered -/
theorem infinitePresentPath_initial_edgeList_prefix {w : ℕ → Fin 3}
    {v : ℕ} (P : InfinitePresentPath w ⟨v⟩) {i j : ℕ} (hij : i ≤ j) :
    pathEdgeList (P.initial i).2 <+: pathEdgeList (P.initial j).2 := by
  rw [P.prefix_edges, P.prefix_edges]
  have hstep (n : ℕ) :
      List.ofFn (fun k : Fin n => P.edge k.val) <+:
        List.ofFn (fun k : Fin n.succ => P.edge k.val) := by
    rw [List.ofFn_succ']
    rw [List.concat_eq_append]
    have hcast : (fun k : Fin n => P.edge (Fin.castSucc k).val) =
        (fun k : Fin n => P.edge k.val) := by
      funext k
      simp
    rw [hcast]
    exact List.prefix_append _ _
  have hle : ∀ m n, m ≤ n →
      List.ofFn (fun k : Fin m => P.edge k.val) <+:
        List.ofFn (fun k : Fin n => P.edge k.val) := by
    intro m n hmn
    induction n generalizing m with
    | zero =>
      have hm : m = 0 := by omega
      subst m
      exact List.prefix_refl _
    | succ n ih =>
      by_cases hmn' : m ≤ n
      · exact (ih m hmn').trans (hstep n)
      · have hm : m = n.succ := by omega
        subst m
        exact List.prefix_refl _
  exact hle i j hij

private theorem infinitePresentPath_initial_index_le_of_mem_vertices
    {w : ℕ → Fin 3} {v₀ : ℕ} (P : InfinitePresentPath w ⟨v₀⟩)
    (N : ℕ) {v : PresentVertex w}
    (hv : v ∈ (P.initial N).2.vertices) :
    ∃ j ≤ N, (P.initial j).1 = v := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hv
  let j := k.val
  have hjN : j ≤ N := by
    have hklt : k.val < N + 1 := by
      simpa [Path.vertices_length, P.prefix_length N] using k.isLt
    omega
  have hjp : j < (P.initial N).2.vertices.length := by
    simpa [j] using k.isLt
  obtain ⟨z, p₁, p₂, hcomp, hp₁⟩ :=
    (P.initial N).2.exists_eq_comp_of_le_length
      (n := j) (by rw [P.prefix_length N]; exact hjN)
  let q := p₁.comp p₂
  have hqLen : q.length = N := by
    dsimp [q]
    rw [← hcomp]
    exact P.prefix_length N
  have hjq : j < q.vertices.length := by
    rw [Path.vertices_length, hqLen]
    dsimp [j]
    omega
  have hget : q.vertices.get ⟨j, hjq⟩ = v := by
    have hgetp : (P.initial N).2.vertices.get ⟨j, hjp⟩ = v := by
      simpa [j] using hk
    have hgetp' : (P.initial N).2.vertices[j] = v := by
      simpa only [List.get_eq_getElem] using hgetp
    have hgetq' : q.vertices[j] = v := by
      simpa only [q, hcomp] using hgetp'
    simpa only [List.get_eq_getElem] using hgetq'
  have hp₁lt : p₁.length < q.vertices.length := by
    rw [Path.vertices_length, hqLen, hp₁]
    omega
  have hidx : (⟨j, hjq⟩ : Fin q.vertices.length) =
      ⟨p₁.length, hp₁lt⟩ := by
    apply Fin.ext
    exact hp₁.symm
  have hzget : q.vertices.get ⟨j, hjq⟩ = z := by
    rw [hidx]
    exact Path.vertices_comp_get_length_eq p₁ p₂
  have hzv : z = v := hzget.symm.trans hget
  let full := List.ofFn (fun i : Fin N => P.edge i.val)
  have hfull : pathEdgeList p₁ ++ pathEdgeList p₂ = full := by
    calc
      pathEdgeList p₁ ++ pathEdgeList p₂ = pathEdgeList q :=
        (pathEdgeList_comp p₁ p₂).symm
      _ = pathEdgeList (P.initial N).2 := by
        change pathEdgeList (p₁.comp p₂) = _
        rw [← hcomp]
      _ = full := P.prefix_edges N
  have hconcat : pathEdgeList p₁ ++ pathEdgeList p₂ =
      full.take j ++ full.drop j := by
    rw [List.take_append_drop j full]
    exact hfull
  have htake : pathEdgeList p₁ = full.take j :=
    List.append_inj_left hconcat (by
      rw [pathEdgeList_length, hp₁, List.length_take]
      simp [full, Nat.min_eq_left hjN])
  have hprefix : List.ofFn (fun i : Fin j => P.edge i.val) =
      full.take j := by
    apply List.ext_get
    · simp [full, Nat.min_eq_left hjN]
    · intro i hi₁ hi₂
      simp [full, List.get_eq_getElem]
  have hpEnd := pathEdgeList_endpoint p₁
  rw [htake, ← hprefix] at hpEnd
  have hqEnd := pathEdgeList_endpoint (P.initial j).2
  rw [P.prefix_edges] at hqEnd
  have hzid : z.id = (P.initial j).1.id := hpEnd.symm.trans hqEnd
  have hzeq : z = (P.initial j).1 :=
    congrArg (fun n : ℕ => (⟨n⟩ : PresentVertex w)) hzid
  exact ⟨j, hjN, hzeq.symm.trans hzv⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Stage inclusion preserves the edge-ID list of any finite dart list. -/
theorem stageInclusion_dartList_edgeIds {w : ℕ → Fin 3} {n m : ℕ}
    (hnm : n ≤ m) (ds : List (StageDart (kmswStage w n).nextEdge)) :
    (ds.map (outerSucc_castDart (kmswStage_nextEdge_mono w hnm))).map
        (fun d => d.1.val) = ds.map (fun d => d.1.val) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  simp [outerSucc_castDart]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Stage inclusion preserves the endpoint side of every dart. -/
theorem stageInclusion_dart_side {w : ℕ → Fin 3} {n m : ℕ}
    (hnm : n ≤ m) (d : StageDart (kmswStage w n).nextEdge) :
    (outerSucc_castDart (kmswStage_nextEdge_mono w hnm) d).2 = d.2 := rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A directed path maps to forward darts under an isomorphism into a KMSW stage. -/
theorem directedPath_stageIso_darts_forward {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {w : ℕ → Fin 3} {n : ℕ}
    {u v : MapVertex M} {len : ℕ}
    (I : DirectedMapWithMissingIso M (kmswStageDirectedMap w n))
    (P : SimpleDirectedDartPath M u v len) :
    ∀ d ∈ P.darts, (I.toEquiv d).2 = false := by
  intro d hd
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  rw [← hi]
  have htail := (I.tail_iff (P.darts.get i)).mpr (P.edge_step i).2.1
  change (kmswStage w n).present (I.toEquiv (P.darts.get i)).1.val = true ∧
    (I.toEquiv (P.darts.get i)).2 = false at htail
  exact htail.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected finite geodesic maps to forward darts in its KMSW stage. -/
theorem selectedGeodesicOfLen_stageIso_darts_forward {ℓ r n m : ℕ}
    {w : ℕ → Fin 3} (R : KMSWMapRep ℓ r n) (x : XDP)
    (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w n)) :
    ∀ d ∈ (selectedGeodesicOfLen R.B x hR).darts, (I.toEquiv d).2 = false :=
  directedPath_stageIso_darts_forward I (selectedGeodesicOfLen R.B x hR)

private theorem directedMapIso_toEquiv_eq_of_connected
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (hconn : M.toCombinatorialMap.IsConnected)
    (I J : DirectedMapWithMissingIso M N) {d : D}
    (hd : I.toEquiv d = J.toEquiv d) : I.toEquiv = J.toEquiv := by
  have hrotSymm (K : DirectedMapWithMissingIso M N) (x : D) :
      K.toEquiv (M.toCombinatorialMap.rot.symm x) =
        N.toCombinatorialMap.rot.symm (K.toEquiv x) := by
    apply N.toCombinatorialMap.rot.injective
    calc
      N.toCombinatorialMap.rot (K.toEquiv (M.toCombinatorialMap.rot.symm x)) =
          K.toEquiv (M.toCombinatorialMap.rot (M.toCombinatorialMap.rot.symm x)) :=
        (K.rot_comm _).symm
      _ = K.toEquiv x := by simp
      _ = N.toCombinatorialMap.rot
          (N.toCombinatorialMap.rot.symm (K.toEquiv x)) := by simp
  have hedgeInvSymm (K : DirectedMapWithMissingIso M N) (x : D) :
      K.toEquiv (M.toCombinatorialMap.edgeInv.symm x) =
        N.toCombinatorialMap.edgeInv.symm (K.toEquiv x) := by
    apply N.toCombinatorialMap.edgeInv.injective
    calc
      N.toCombinatorialMap.edgeInv
          (K.toEquiv (M.toCombinatorialMap.edgeInv.symm x)) =
          K.toEquiv (M.toCombinatorialMap.edgeInv
            (M.toCombinatorialMap.edgeInv.symm x)) := (K.edgeInv_comm _).symm
      _ = K.toEquiv x := by simp
      _ = N.toCombinatorialMap.edgeInv
          (N.toCombinatorialMap.edgeInv.symm (K.toEquiv x)) := by simp
  let R := fun x y : D =>
    y = M.toCombinatorialMap.rot x ∨
    y = M.toCombinatorialMap.rot.symm x ∨
    y = M.toCombinatorialMap.edgeInv x ∨
    y = M.toCombinatorialMap.edgeInv.symm x
  have hstep : ∀ {x y}, R x y → I.toEquiv x = J.toEquiv x →
      I.toEquiv y = J.toEquiv y := by
    intro x y hxy hx
    rcases hxy with h | h | h | h
    · subst y
      calc
        I.toEquiv (M.toCombinatorialMap.rot x) =
            N.toCombinatorialMap.rot (I.toEquiv x) := I.rot_comm x
        _ = N.toCombinatorialMap.rot (J.toEquiv x) := congrArg _ hx
        _ = J.toEquiv (M.toCombinatorialMap.rot x) := (J.rot_comm x).symm
    · subst y
      calc
        I.toEquiv (M.toCombinatorialMap.rot.symm x) =
            N.toCombinatorialMap.rot.symm (I.toEquiv x) := hrotSymm I x
        _ = N.toCombinatorialMap.rot.symm (J.toEquiv x) := congrArg _ hx
        _ = J.toEquiv (M.toCombinatorialMap.rot.symm x) :=
          (hrotSymm J x).symm
    · subst y
      calc
        I.toEquiv (M.toCombinatorialMap.edgeInv x) =
            N.toCombinatorialMap.edgeInv (I.toEquiv x) := I.edgeInv_comm x
        _ = N.toCombinatorialMap.edgeInv (J.toEquiv x) := congrArg _ hx
        _ = J.toEquiv (M.toCombinatorialMap.edgeInv x) := (J.edgeInv_comm x).symm
    · subst y
      calc
        I.toEquiv (M.toCombinatorialMap.edgeInv.symm x) =
            N.toCombinatorialMap.edgeInv.symm (I.toEquiv x) := hedgeInvSymm I x
        _ = N.toCombinatorialMap.edgeInv.symm (J.toEquiv x) := congrArg _ hx
        _ = J.toEquiv (M.toCombinatorialMap.edgeInv.symm x) :=
          (hedgeInvSymm J x).symm
  have hreach : ∀ x, Relation.ReflTransGen R d x →
      I.toEquiv x = J.toEquiv x := by
    intro x h
    induction h with
    | refl => exact hd
    | tail _ hxy ih => exact hstep hxy ih
  ext x
  exact hreach x (hconn d x)

private theorem bipolarBoundaryBaseIso_toEquiv_eq
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I J : BipolarBoundaryBaseIso B B') : I.toEquiv = J.toEquiv := by
  let d := B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)
  have hpos : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact Nat.zero_lt_of_lt B.left_length_pos
  have hfirst : B.leftPath.darts[0]? = some d := List.getElem?_eq_getElem hpos
  have hmaps : B.leftPath.darts.map I.toEquiv = B.leftPath.darts.map J.toEquiv := by
    rw [I.leftDarts, J.leftDarts]
  have hhead := congrArg (fun ds : List E => ds[0]?) hmaps
  simp only [List.getElem?_map, hfirst, Option.map_some] at hhead
  have hd : I.toEquiv d = J.toEquiv d := Option.some.inj hhead
  let I' : DirectedMapWithMissingIso B.map B'.map := {
    toEquiv := I.toEquiv
    rot_comm := I.rot_comm
    edgeInv_comm := I.edgeInv_comm
    missing_iff := I.missing_iff
    tail_iff := I.tail_iff
    outer_iff := I.outer_iff }
  let J' : DirectedMapWithMissingIso B.map B'.map := {
    toEquiv := J.toEquiv
    rot_comm := J.rot_comm
    edgeInv_comm := J.edgeInv_comm
    missing_iff := J.missing_iff
    tail_iff := J.tail_iff
    outer_iff := J.outer_iff }
  exact directedMapIso_toEquiv_eq_of_connected B.planar.1 I' J' hd

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The record-stage dart map agrees with the selected representative's induced -/
theorem selectedCutRep_recordStage_toEquiv_eq
    {ℓ r t : ℕ} {w : ℕ → Fin 3} (ht : 1 ≤ t)
    (c : KMSWWalkClass ℓ r t)
    (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R : KMSWMapRep ℓ r t)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap w (t - 1)))
    (hboundary : ∀ a : ThinMapSide, (boundaryDarts R.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) :
    ∃ H : BipolarBoundaryBaseIso R.B (kmswWalkClassRep ht c).B,
      ∀ d, I.toEquiv d =
        (kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc).toEquiv
          ((kmswWalkClassRep_mapIso ht c).toEquiv (H.toEquiv d)) := by
  let E := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc
  let J := kmswWalkClassRep_mapIso ht c
  let Rep := kmswWalkClassRep ht c
  let G := I.trans (E.symm.trans J.symm)
  have hout : Rep.B.map.IsOuter (G.toEquiv R.B.map.outer) :=
    (G.outer_iff R.B.map.outer).mpr Equiv.Perm.SameCycle.rfl
  let H := bipolarBoundaryBaseIsoOfRot R.B Rep.B G.toEquiv
    G.rot_comm G.edgeInv_comm G.tail_iff
    ⟨R.B.map.outer, Equiv.Perm.SameCycle.rfl, hout⟩
  let Hmap : DirectedMapWithMissingIso R.B.map Rep.B.map := {
    toEquiv := H.toEquiv
    rot_comm := H.rot_comm
    edgeInv_comm := H.edgeInv_comm
    missing_iff := H.missing_iff
    tail_iff := H.tail_iff
    outer_iff := H.outer_iff }
  let F := (Hmap.trans J).trans E
  let f : Fin R.dartCount → StageDart (kmswStage w (t - 1)).nextEdge :=
    fun d => E.toEquiv (J.toEquiv (H.toEquiv d))
  have hstage : kmswStage (codeExtend c) (t - 1) = kmswStage w (t - 1) :=
    kmswStage_eq_of_prefix (codeExtend c) w (t - 1) hc
  have hElabels (ds : List (StageDart (kmswStage (codeExtend c) (t - 1)).nextEdge)) :
      (ds.map E.toEquiv).map (fun d => (d.1.val, d.2)) =
        ds.map (fun d => (d.1.val, d.2)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    obtain ⟨he, hb⟩ := kmswStageDirectedMapIsoOfPrefix_val
      (codeExtend c) w (t - 1) hc d
    exact Prod.ext he hb
  have hFlabels : (R.B.leftPath.darts.map f).map
      (fun d => (d.1.val, d.2)) =
        (kmswStage w (t - 1)).UL.map (fun e => (e, false)) := by
    calc
      (R.B.leftPath.darts.map f).map (fun d => (d.1.val, d.2)) =
          (((R.B.leftPath.darts.map H.toEquiv).map J.toEquiv).map E.toEquiv).map
            (fun d => (d.1.val, d.2)) := by
        simp only [f, List.map_map, Function.comp_def]
      _ = (((Rep.B.leftPath.darts.map J.toEquiv).map E.toEquiv).map
            (fun d => (d.1.val, d.2))) := by rw [H.leftDarts]
      _ = (Rep.B.leftPath.darts.map J.toEquiv).map
            (fun d => (d.1.val, d.2)) := hElabels _
      _ = (kmswStage (codeExtend c) (t - 1)).UL.map
            (fun e => (e, false)) := by
        simpa only [boundaryDarts, List.map_map, Function.comp_def] using
          cut_walkClassRep_boundary_stage ht c .left
      _ = (kmswStage w (t - 1)).UL.map (fun e => (e, false)) := by
        rw [hstage]
  let d := R.B.leftPath.firstDart (Nat.zero_lt_of_lt R.B.left_length_pos)
  have hpos : 0 < R.B.leftPath.darts.length := by
    rw [R.B.leftPath.darts_length]
    exact Nat.zero_lt_of_lt R.B.left_length_pos
  have hfirst : R.B.leftPath.darts[0]? = some d := List.getElem?_eq_getElem hpos
  have hboundaryLeft := hboundary .left
  change R.B.leftPath.darts.map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) = _ at hboundaryLeft
  have hhead := congrArg (fun ds : List (ℕ × Bool) => ds[0]?)
    (hboundaryLeft.trans hFlabels.symm)
  simp only [List.getElem?_map, hfirst, Option.map_some] at hhead
  have hpair : ((I.toEquiv d).1.val, (I.toEquiv d).2) =
      ((f d).1.val, (f d).2) := Option.some.inj hhead
  have hd : I.toEquiv d = f d := by
    have hval := congrArg (fun p : ℕ × Bool => p.1) hpair
    have hside := congrArg (fun p : ℕ × Bool => p.2) hpair
    have hindex : (I.toEquiv d).1 = (f d).1 := Fin.ext hval
    exact Prod.ext hindex hside
  have hmaps : I.toEquiv = F.toEquiv := by
    exact directedMapIso_toEquiv_eq_of_connected R.B.planar.1 I F (by
      simpa only [F, Hmap, DirectedMapWithMissingIso.trans,
        Equiv.trans_apply] using hd)
  refine ⟨H, ?_⟩
  intro e
  have he := congrArg
    (fun g : Fin R.dartCount ≃ StageDart (kmswStage w (t - 1)).nextEdge => g.toFun e)
    hmaps
  change I.toEquiv e = E.toEquiv (J.toEquiv (H.toEquiv e))
  calc
    I.toEquiv e = F.toEquiv e := he
    _ = E.toEquiv (J.toEquiv (H.toEquiv e)) := rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A selected-cut representative is base-isomorphic to its stopped walk-class -/
theorem selectedCutRep_baseIso_stoppedWalkClassRep
    {ℓ r t : ℕ} {w : ℕ → Fin 3} (ht : 1 ≤ t)
    (c : KMSWWalkClass ℓ r t)
    (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R : KMSWMapRep ℓ r t)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap w (t - 1))) :
    Nonempty (BipolarBoundaryBaseIso R.B (kmswWalkClassRep ht c).B) := by
  let E := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc
  let J := kmswWalkClassRep_mapIso ht c
  let G := I.trans (E.symm.trans J.symm)
  have hout : (kmswWalkClassRep ht c).B.map.IsOuter (G.toEquiv R.B.map.outer) :=
    (G.outer_iff R.B.map.outer).mpr Equiv.Perm.SameCycle.rfl
  exact ⟨bipolarBoundaryBaseIsoOfRot R.B (kmswWalkClassRep ht c).B G.toEquiv
    G.rot_comm G.edgeInv_comm G.tail_iff
    ⟨R.B.map.outer, Equiv.Perm.SameCycle.rfl, hout⟩⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Base-isomorphic selected geodesics have identical edge lists in the shared -/
theorem selectedCutRep_stageEdgeList_eq_stoppedWalkClassRep
    {ℓ r t : ℕ} {w : ℕ → Fin 3} (ht : 1 ≤ t)
    (c : KMSWWalkClass ℓ r t)
    (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R : KMSWMapRep ℓ r t) (x : XDP)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap w (t - 1))) :
    let E := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc
    let J := kmswWalkClassRep_mapIso ht c
    ∃ H : BipolarBoundaryBaseIso R.B (kmswWalkClassRep ht c).B,
      ∃ hlen : xdpLengthBase R.B x =
        xdpLengthBase (kmswWalkClassRep ht c).B x,
        ((((selectedGeodesicOfLen R.B x hlen).darts.map H.toEquiv).map
          J.toEquiv).map E.toEquiv).map (fun d => d.1.val) =
        (((selectedGeodesicOfLen (kmswWalkClassRep ht c).B x rfl).darts.map
          J.toEquiv).map E.toEquiv).map (fun d => d.1.val) := by
  dsimp only
  let E := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc
  let J := kmswWalkClassRep_mapIso ht c
  obtain ⟨H⟩ := selectedCutRep_baseIso_stoppedWalkClassRep ht c hc R I
  have hlen : xdpLengthBase R.B x = xdpLengthBase (kmswWalkClassRep ht c).B x := by
    cases x with
    | ldp => simpa only [xdpLengthBase] using (ldpLengthBase_eq_of_baseIso H).symm
    | sdp => simpa only [xdpLengthBase] using (sdpLengthBase_eq_of_baseIso H).symm
  let P := selectedGeodesicOfLen R.B x hlen
  let Q := selectedGeodesicOfLen (kmswWalkClassRep ht c).B x rfl
  have hmap : Q.darts = P.darts.map H.toEquiv :=
    dartLists_eq_of_isLexLeftmostXDPGeodesic_baseIso H x P Q
      (selectedGeodesicOfLen_isLexLeftmost R.B x hlen)
      (selectedGeodesicOfLen_isLexLeftmost (kmswWalkClassRep ht c).B x rfl)
  refine ⟨H, hlen, ?_⟩
  rw [← hmap]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The record-stage dart map carries the selected edge list to its stopped -/
theorem selectedCutRep_recordStage_edgeIds_eq_stoppedWalkClassRep
    {ℓ r t : ℕ} {w : ℕ → Fin 3} (ht : 1 ≤ t)
    (c : KMSWWalkClass ℓ r t)
    (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R : KMSWMapRep ℓ r t) (x : XDP)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap w (t - 1)))
    (hboundary : ∀ a : ThinMapSide, (boundaryDarts R.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) :
    ∃ hlen : xdpLengthBase R.B x =
        xdpLengthBase (kmswWalkClassRep ht c).B x,
      ((selectedGeodesicOfLen R.B x hlen).darts.map I.toEquiv).map
          (fun d => d.1.val) =
        (((selectedGeodesicOfLen (kmswWalkClassRep ht c).B x rfl).darts.map
          (kmswWalkClassRep_mapIso ht c).toEquiv).map
            (kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc).toEquiv).map
          (fun d => d.1.val) := by
  obtain ⟨H₁, hlen, hstage⟩ :=
    selectedCutRep_stageEdgeList_eq_stoppedWalkClassRep ht c hc R x I
  obtain ⟨H₂, hI⟩ :=
    selectedCutRep_recordStage_toEquiv_eq ht c hc R I hboundary
  have hH : H₁.toEquiv = H₂.toEquiv :=
    bipolarBoundaryBaseIso_toEquiv_eq H₁ H₂
  let E := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc
  let J := kmswWalkClassRep_mapIso ht c
  have hmap : (selectedGeodesicOfLen R.B x hlen).darts.map I.toEquiv =
      (((selectedGeodesicOfLen R.B x hlen).darts.map H₁.toEquiv).map J.toEquiv).map
        E.toEquiv := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro d hd
    change I.toEquiv d = E.toEquiv (J.toEquiv (H₁.toEquiv d))
    have hHd : H₁.toEquiv d = H₂.toEquiv d := congrArg (fun e => e d) hH
    calc
      I.toEquiv d = E.toEquiv (J.toEquiv (H₂.toEquiv d)) := hI d
      _ = E.toEquiv (J.toEquiv (H₁.toEquiv d)) :=
        congrArg (fun z => E.toEquiv (J.toEquiv z)) hHd.symm
  refine ⟨hlen, ?_⟩
  have hids := congrArg (fun ds => ds.map (fun d => d.1.val)) hmap
  exact hids.trans hstage

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected path at a record cut is the prefix of the infinite LDP path. -/
theorem selectedCutRep_recordStage_edgeIds_eq_ldpPrefix
    {ℓ r t : ℕ} {w : ℕ → Fin 3} (ht : 1 ≤ t)
    (hA : ∀ j < t, R w t ≤ R w j - 1)
    (hB : ∀ j, t ≤ j → L w t ≤ L w j)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (c : KMSWWalkClass ℓ r t)
    (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R₀ : KMSWMapRep ℓ r t)
    (I : DirectedMapWithMissingIso R₀.B.map
      (kmswStageDirectedMap w (t - 1)))
    (hboundary : ∀ a : ThinMapSide, (boundaryDarts R₀.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false)))
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) :
    ∃ hlen : xdpLengthBase R₀.B .ldp =
        xdpLengthBase (kmswWalkClassRep ht c).B .ldp,
      let P := selectedGeodesicOfLen R₀.B .ldp hlen
      ∃ i, P.darts.length = i ∧
        ((kmswLeftmostLdpPath w hfin hL htrans hR 0 hg).initial i).1 =
          recordVertex w t ∧
        (∀ j < i, ((kmswLeftmostLdpPath w hfin hL htrans hR 0 hg).initial j).1 ≠
          recordVertex w t) ∧
        (P.darts.map I.toEquiv).map
            (fun d => d.1.val) =
          List.ofFn (fun j : Fin P.darts.length =>
            (kmswLeftmostLdpPath w hfin hL htrans hR 0 hg).edge j.val) := by
  obtain ⟨Hlen, hselected⟩ :=
    selectedCutRep_recordStage_edgeIds_eq_stoppedWalkClassRep
      ht c hc R₀ XDP.ldp I hboundary
  let Q := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
  let Rep := kmswWalkClassRep ht c
  let Sel := selectedGeodesicOfLen Rep.B .ldp rfl
  let Pfin := selectedGeodesicOfLen R₀.B .ldp Hlen
  let d := xdpLengthBase Rep.B .ldp
  have hcut : mapCutVertex w hfin (recordVertex w t).id := by
    have hIsCut : IsCutVertex w (activeInitial w t) :=
      ⟨onLeftBoundary_activeInitial_of_barrier w htrans t hB,
        onRightBoundary_activeInitial_of_record w t hA⟩
    have hcut' := (mapCutVertex_iff w hfin htrans hR hL
      (activeInitial w t)).mpr hIsCut
    simpa only [recordVertex, CutConverse.activeInitial_eq] using hcut'
  have htraceInf := selectedCut_pastLdpTrace_eq_infinitePrefix
    w hfin hL htrans hR t hcut hg
  dsimp only at htraceInf
  rcases htraceInf with ⟨i, hi, hfirst, htraceInf⟩
  have hprev : t - 1 + 1 = t := by omega
  have hdown := record_stage_before_empty_UR_public w t hA (by omega)
  have hnext := activeInitial_next_of_empty_UR_public w (t - 1) hdown.1
    (by simpa using hdown.2)
  have hsink : (recordVertex w t).id =
      (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active := by
    calc
      (recordVertex w t).id = activeInitial w t :=
        (CutConverse.activeInitial_eq w t).symm
      _ = (kmswStage w (t - 1)).east (act w (t - 1)) := by
        simpa only [hprev] using hnext
      _ = (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active := rfl
  let E := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc
  let J := kmswWalkClassRep_mapIso ht c
  have hrepTrace := stageSinkLeftmostXDPTrace_eq_selected ht c .ldp
  change stageSinkLeftmostXDPTrace (codeExtend c) (t - 1) .ldp
      ⟨(kmswStage (codeExtend c) (t - 1)).east
        (kmswStage (codeExtend c) (t - 1)).active⟩ d =
    some ((kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active,
      Sel.darts.map J.toEquiv) at hrepTrace
  have hprefixTrace := stageSinkLeftmostXDPTrace_eq_of_prefix
    (codeExtend c) w (t - 1) hc .ldp
    ((kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active) d
  rw [hrepTrace] at hprefixTrace
  have hstages : kmswStage (codeExtend c) (t - 1) = kmswStage w (t - 1) :=
    kmswStage_eq_of_prefix (codeExtend c) w (t - 1) hc
  have hsinkStages : (kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active =
      (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active := by
    rw [hstages]
  rw [hsinkStages] at hprefixTrace
  have hpast : pastStageLeftmostXDPTrace w t .ldp d =
      some ((recordVertex w t).id, ((Sel.darts.map J.toEquiv).map E.toEquiv)) := by
    rw [← hsink] at hprefixTrace
    rw [stageSinkLeftmostXDPTrace_record] at hprefixTrace
    exact hprefixTrace.symm
  have hafter : ∀ n, i < n → pastStageLeftmostXDPTrace w t .ldp n = none := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro hn
      by_cases hni : n = i
      · subst n
        obtain ⟨ds, _, _, hstop⟩ := htraceInf i le_rfl
        have hnil := hstop rfl
        simpa only [pastStageLeftmostXDPTrace, hnil, Option.bind_none]
      · have hni' : i < n := by omega
        simp only [pastStageLeftmostXDPTrace, ih hni', Option.bind_none]
  have hdle : d ≤ i := by
    by_contra hnot
    have hlt : i < d := Nat.lt_of_not_ge hnot
    rw [hafter d hlt] at hpast
    contradiction
  obtain ⟨ds, htraceAtD, hidsAtD, _⟩ := htraceInf d hdle
  have hpair : ((recordVertex w t).id, (Sel.darts.map J.toEquiv).map E.toEquiv) =
      ((Q.initial d).1.id, ds) := Option.some.inj (hpast.symm.trans htraceAtD)
  rcases Prod.mk.inj hpair with ⟨hvertexId, hds⟩
  have hvertex : (Q.initial d).1 = recordVertex w t :=
    congrArg PresentVertex.mk hvertexId.symm
  have hdi : d = i := by
    by_contra hne
    have hlt : d < i := by omega
    exact hfirst d hlt hvertex
  have hstageIds :
      ((Sel.darts.map J.toEquiv).map E.toEquiv).map (fun e => e.1.val) =
        ds.map (fun e => e.1.val) := by
    have h := congrArg (fun es : List (StageDart (kmswStage w (t - 1)).nextEdge) =>
      es.map (fun e => e.1.val)) hds
    exact h
  have hpathIds : ds.map (fun e => e.1.val) = pathEdgeList (Q.initial d).2 := hidsAtD
  have hprefixEdges := Q.prefix_edges d
  have hfinal :
      (Pfin.darts.map I.toEquiv).map
          (fun e => e.1.val) =
        List.ofFn (fun j : Fin i => Q.edge j.val) := by
    calc
      _ = (((Sel.darts.map J.toEquiv).map E.toEquiv).map
          (fun e => e.1.val)) := hselected
      _ = ds.map (fun e => e.1.val) := hstageIds
      _ = pathEdgeList (Q.initial d).2 := hpathIds
      _ = List.ofFn (fun j : Fin d => Q.edge j.val) := hprefixEdges
      _ = List.ofFn (fun j : Fin i => Q.edge j.val) := by rw [hdi]
  have hlen : Pfin.darts.length = i := by
    have h := congrArg List.length hfinal
    simpa only [List.length_map, List.length_ofFn] using h
  have hcastList : List.ofFn (fun j : Fin i => Q.edge j.val) =
      List.ofFn (fun j : Fin Pfin.darts.length => Q.edge j.val) := by
    rw [List.ofFn_congr hlen.symm (fun j : Fin i => Q.edge j.val)]
    simp only [Fin.val_cast]
  refine ⟨Hlen, ?_⟩
  dsimp only
  refine ⟨i, hlen, hi, hfirst, ?_⟩
  exact hfinal.trans hcastList

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected path at a record cut is the prefix of the infinite SDP path. -/
theorem selectedCutRep_recordStage_edgeIds_eq_sdpPrefix
    {ℓ r t : ℕ} {w : ℕ → Fin 3} (ht : 1 ≤ t)
    (hA : ∀ j < t, R w t ≤ R w j - 1)
    (hB : ∀ j, t ≤ j → L w t ≤ L w j)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (c : KMSWWalkClass ℓ r t)
    (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R₀ : KMSWMapRep ℓ r t)
    (I : DirectedMapWithMissingIso R₀.B.map
      (kmswStageDirectedMap w (t - 1)))
    (hboundary : ∀ a : ThinMapSide, (boundaryDarts R₀.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false)))
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    ∃ hlen : xdpLengthBase R₀.B .sdp =
        xdpLengthBase (kmswWalkClassRep ht c).B .sdp,
      let P := selectedGeodesicOfLen R₀.B .sdp hlen
      ∃ i, P.darts.length = i ∧
        ((kmswLeftmostSdpPath w hfin hL htrans hR 0 hg).initial i).1 =
          recordVertex w t ∧
        (∀ j < i, ((kmswLeftmostSdpPath w hfin hL htrans hR 0 hg).initial j).1 ≠
          recordVertex w t) ∧
        (P.darts.map I.toEquiv).map
            (fun d => d.1.val) =
          List.ofFn (fun j : Fin P.darts.length =>
            (kmswLeftmostSdpPath w hfin hL htrans hR 0 hg).edge j.val) := by
  obtain ⟨Hlen, hselected⟩ :=
    selectedCutRep_recordStage_edgeIds_eq_stoppedWalkClassRep
      ht c hc R₀ XDP.sdp I hboundary
  let Q := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
  let Rep := kmswWalkClassRep ht c
  let Sel := selectedGeodesicOfLen Rep.B .sdp rfl
  let Pfin := selectedGeodesicOfLen R₀.B .sdp Hlen
  let d := xdpLengthBase Rep.B .sdp
  have hcut : mapCutVertex w hfin (recordVertex w t).id := by
    have hIsCut : IsCutVertex w (activeInitial w t) :=
      ⟨onLeftBoundary_activeInitial_of_barrier w htrans t hB,
        onRightBoundary_activeInitial_of_record w t hA⟩
    have hcut' := (mapCutVertex_iff w hfin htrans hR hL
      (activeInitial w t)).mpr hIsCut
    simpa only [recordVertex, CutConverse.activeInitial_eq] using hcut'
  have htraceInf := selectedCut_pastSdpTrace_eq_infinitePrefix
    w hfin hL htrans hR t hcut hg
  dsimp only at htraceInf
  rcases htraceInf with ⟨i, hi, hfirst, htraceInf⟩
  have hprev : t - 1 + 1 = t := by omega
  have hdown := record_stage_before_empty_UR_public w t hA (by omega)
  have hnext := activeInitial_next_of_empty_UR_public w (t - 1) hdown.1
    (by simpa using hdown.2)
  have hsink : (recordVertex w t).id =
      (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active := by
    calc
      (recordVertex w t).id = activeInitial w t :=
        (CutConverse.activeInitial_eq w t).symm
      _ = (kmswStage w (t - 1)).east (act w (t - 1)) := by
        simpa only [hprev] using hnext
      _ = (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active := rfl
  let E := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc
  let J := kmswWalkClassRep_mapIso ht c
  have hrepTrace := stageSinkLeftmostXDPTrace_eq_selected ht c .sdp
  change stageSinkLeftmostXDPTrace (codeExtend c) (t - 1) .sdp
      ⟨(kmswStage (codeExtend c) (t - 1)).east
        (kmswStage (codeExtend c) (t - 1)).active⟩ d =
    some ((kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active,
      Sel.darts.map J.toEquiv) at hrepTrace
  have hprefixTrace := stageSinkLeftmostXDPTrace_eq_of_prefix
    (codeExtend c) w (t - 1) hc .sdp
    ((kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active) d
  rw [hrepTrace] at hprefixTrace
  have hstages : kmswStage (codeExtend c) (t - 1) = kmswStage w (t - 1) :=
    kmswStage_eq_of_prefix (codeExtend c) w (t - 1) hc
  have hsinkStages : (kmswStage (codeExtend c) (t - 1)).east
      (kmswStage (codeExtend c) (t - 1)).active =
      (kmswStage w (t - 1)).east (kmswStage w (t - 1)).active := by
    rw [hstages]
  rw [hsinkStages] at hprefixTrace
  have hpast : pastStageLeftmostXDPTrace w t .sdp d =
      some ((recordVertex w t).id, ((Sel.darts.map J.toEquiv).map E.toEquiv)) := by
    rw [← hsink] at hprefixTrace
    rw [stageSinkLeftmostXDPTrace_record] at hprefixTrace
    exact hprefixTrace.symm
  have hafter : ∀ n, i < n → pastStageLeftmostXDPTrace w t .sdp n = none := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro hn
      by_cases hni : n = i
      · subst n
        obtain ⟨ds, _, _, hstop⟩ := htraceInf i le_rfl
        have hnil := hstop rfl
        simpa only [pastStageLeftmostXDPTrace, hnil, Option.bind_none]
      · have hni' : i < n := by omega
        simp only [pastStageLeftmostXDPTrace, ih hni', Option.bind_none]
  have hdle : d ≤ i := by
    by_contra hnot
    have hlt : i < d := Nat.lt_of_not_ge hnot
    rw [hafter d hlt] at hpast
    contradiction
  obtain ⟨ds, htraceAtD, hidsAtD, _⟩ := htraceInf d hdle
  have hpair : ((recordVertex w t).id, (Sel.darts.map J.toEquiv).map E.toEquiv) =
      ((Q.initial d).1.id, ds) := Option.some.inj (hpast.symm.trans htraceAtD)
  rcases Prod.mk.inj hpair with ⟨hvertexId, hds⟩
  have hvertex : (Q.initial d).1 = recordVertex w t :=
    congrArg PresentVertex.mk hvertexId.symm
  have hdi : d = i := by
    by_contra hne
    have hlt : d < i := by omega
    exact hfirst d hlt hvertex
  have hstageIds :
      ((Sel.darts.map J.toEquiv).map E.toEquiv).map (fun e => e.1.val) =
        ds.map (fun e => e.1.val) := by
    have h := congrArg (fun es : List (StageDart (kmswStage w (t - 1)).nextEdge) =>
      es.map (fun e => e.1.val)) hds
    exact h
  have hpathIds : ds.map (fun e => e.1.val) = pathEdgeList (Q.initial d).2 := hidsAtD
  have hprefixEdges := Q.prefix_edges d
  have hfinal :
      (Pfin.darts.map I.toEquiv).map
          (fun e => e.1.val) =
        List.ofFn (fun j : Fin i => Q.edge j.val) := by
    calc
      _ = (((Sel.darts.map J.toEquiv).map E.toEquiv).map
          (fun e => e.1.val)) := hselected
      _ = ds.map (fun e => e.1.val) := hstageIds
      _ = pathEdgeList (Q.initial d).2 := hpathIds
      _ = List.ofFn (fun j : Fin d => Q.edge j.val) := hprefixEdges
      _ = List.ofFn (fun j : Fin i => Q.edge j.val) := by rw [hdi]
  have hlen : Pfin.darts.length = i := by
    have h := congrArg List.length hfinal
    simpa only [List.length_map, List.length_ofFn] using h
  have hcastList : List.ofFn (fun j : Fin i => Q.edge j.val) =
      List.ofFn (fun j : Fin Pfin.darts.length => Q.edge j.val) := by
    rw [List.ofFn_congr hlen.symm (fun j : Fin i => Q.edge j.val)]
    simp only [Fin.val_cast]
  refine ⟨Hlen, ?_⟩
  dsimp only
  refine ⟨i, hlen, hi, hfirst, ?_⟩
  exact hfinal.trans hcastList

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The second selected cut has the SDP edge list of the same infinite leftmost path -/
theorem selectedCutRep_secondRecordStage_edgeIds_eq_sdpPrefix
    {ℓ r t' : ℕ} {w : ℕ → Fin 3} (ht' : 1 ≤ t')
    (hA' : ∀ j < t', R w t' ≤ R w j - 1)
    (hB' : ∀ j, t' ≤ j → L w t' ≤ L w j)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (c : KMSWWalkClass ℓ r t')
    (hc : ∀ i < t' - 1, codeExtend c i = w i)
    (R₀ : KMSWMapRep ℓ r t')
    (I : DirectedMapWithMissingIso R₀.B.map
      (kmswStageDirectedMap w (t' - 1)))
    (hboundary : ∀ a : ThinMapSide, (boundaryDarts R₀.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t' - 1)).UL
          | .right => (kmswStage w (t' - 1)).LR).map (fun e => (e, false)))
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    ∃ hlen : xdpLengthBase R₀.B .sdp =
        xdpLengthBase (kmswWalkClassRep ht' c).B .sdp,
      let P := selectedGeodesicOfLen R₀.B .sdp hlen
      ∃ i, P.darts.length = i ∧
        ((kmswLeftmostSdpPath w hfin hL htrans hR 0 hg).initial i).1 =
          recordVertex w t' ∧
        (∀ j < i, ((kmswLeftmostSdpPath w hfin hL htrans hR 0 hg).initial j).1 ≠
          recordVertex w t') ∧
        (P.darts.map I.toEquiv).map (fun d => d.1.val) =
          List.ofFn (fun j : Fin P.darts.length =>
            (kmswLeftmostSdpPath w hfin hL htrans hR 0 hg).edge j.val) := by
  exact selectedCutRep_recordStage_edgeIds_eq_sdpPrefix ht' hA' hB' hfin
    hL htrans hR c hc R₀ I hboundary hg

private theorem infinitePresentPath_firstVisit_index_le_of_cut
    {w : ℕ → Fin 3} (hfin : ∀ u, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) {v : PresentVertex w}
    (hcut : mapCutVertex w hfin v.id) (Q : InfinitePresentPath w ⟨0⟩)
    {i j : ℕ}
    (hfirst : ∀ k < i, (Q.initial k).1 ≠ v)
    (hreach : Reachable v (Q.initial j).1) : i ≤ j := by
  have hmem := mapCutVertex_separates_reachable w hfin hL htrans hR hcut
    (Q.initial j).1 hreach (Q.initial j).2
  have hmem' : v ∈ (Q.initial j).2.vertices := by
    simpa using hmem
  obtain ⟨k, hkj, hk⟩ :=
    infinitePresentPath_initial_index_le_of_mem_vertices Q j hmem'
  by_contra hnot
  have hki : k < i := by omega
  exact hfirst k hki hk

private theorem recordVertex_is_mapCutVertex_of_records
    (w : ℕ → Fin 3) (t : ℕ)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hA : ∀ j < t, R w t ≤ R w j - 1)
    (hB : ∀ j, t ≤ j → L w t ≤ L w j) :
    mapCutVertex w hfin (recordVertex w t).id := by
  have hIsCut : IsCutVertex w (activeInitial w t) :=
    ⟨onLeftBoundary_activeInitial_of_barrier w htrans t hB,
      onRightBoundary_activeInitial_of_record w t hA⟩
  have hcut := (mapCutVertex_iff w hfin htrans hR hL
    (activeInitial w t)).mpr hIsCut
  simpa only [recordVertex, CutConverse.activeInitial_eq] using hcut

private theorem recordVertex_reachable_of_le
    (w : ℕ → Fin 3) {t t' : ℕ} (htt' : t ≤ t')
    (hA : ∀ j < t, R w t ≤ R w j - 1)
    (hA' : ∀ j < t', R w t' ≤ R w j - 1) :
    Reachable (recordVertex w t) (recordVertex w t') := by
  by_cases heq : t = t'
  · subst t'
    exact ⟨Path.nil⟩
  · exact recordVertex_reachable w (lt_of_le_of_ne htt' heq) hA hA'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The earlier selected path is no longer than the later one at ordered record cuts. -/
theorem selectedCutRep_recordStage_dartLength_le
    {ℓ r t ℓ' r' t' m m' : ℕ} {w : ℕ → Fin 3}
    (htt' : t ≤ t') (ht : 1 ≤ t) (ht' : 1 ≤ t')
    (hA : ∀ j < t, R w t ≤ R w j - 1)
    (hB : ∀ j, t ≤ j → L w t ≤ L w j)
    (hA' : ∀ j < t', R w t' ≤ R w j - 1)
    (hB' : ∀ j, t' ≤ j → L w t' ≤ L w j)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hRbound : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (c : KMSWWalkClass ℓ r t)
    (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R₀ : KMSWMapRep ℓ r t)
    (I : DirectedMapWithMissingIso R₀.B.map
      (kmswStageDirectedMap w (t - 1)))
    (hboundary : ∀ a : ThinMapSide, (boundaryDarts R₀.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false)))
    (c' : KMSWWalkClass ℓ' r' t')
    (hc' : ∀ i < t' - 1, codeExtend c' i = w i)
    (S₀ : KMSWMapRep ℓ' r' t')
    (J : DirectedMapWithMissingIso S₀.B.map
      (kmswStageDirectedMap w (t' - 1)))
    (hboundary' : ∀ a : ThinMapSide, (boundaryDarts S₀.B a).map
      (fun d => ((J.toEquiv d).1.val, (J.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t' - 1)).UL
          | .right => (kmswStage w (t' - 1)).LR).map (fun e => (e, false)))
    (x : XDP) (hR : xdpLengthBase R₀.B x = m)
    (hS : xdpLengthBase S₀.B x = m')
    (hgL : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments)
    (hgS : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    (selectedGeodesicOfLen R₀.B x hR).darts.length ≤
      (selectedGeodesicOfLen S₀.B x hS).darts.length := by
  have hcut := recordVertex_is_mapCutVertex_of_records w t hfin hL htrans
    hRbound hA hB
  have hreach := recordVertex_reachable_of_le w htt' hA hA'
  cases x with
  | ldp =>
    obtain ⟨hlenR, hprefixR⟩ := selectedCutRep_recordStage_edgeIds_eq_ldpPrefix
      ht hA hB hfin hL htrans hRbound c hc R₀ I hboundary hgL
    obtain ⟨hlenS, hprefixS⟩ := selectedCutRep_recordStage_edgeIds_eq_ldpPrefix
      ht' hA' hB' hfin hL htrans hRbound c' hc' S₀ J hboundary' hgL
    rcases hprefixR with ⟨i, hiLen, _, hiFirst, _⟩
    rcases hprefixS with ⟨j, hjLen, hjVertex, hjFirst, _⟩
    have hreachQ : Reachable (recordVertex w t)
        ((kmswLeftmostLdpPath w hfin hL htrans hRbound 0 hgL).initial j).1 := by
      rw [hjVertex]
      exact hreach
    have hij := infinitePresentPath_firstVisit_index_le_of_cut hfin hL
      htrans hRbound hcut _ hiFirst hreachQ
    have hlenEqR : (selectedGeodesicOfLen R₀.B .ldp hR).darts.length =
        (selectedGeodesicOfLen R₀.B .ldp hlenR).darts.length := by
      rw [selectedGeodesicOfLen_darts, selectedGeodesicOfLen_darts]
    have hlenEqS : (selectedGeodesicOfLen S₀.B .ldp hS).darts.length =
        (selectedGeodesicOfLen S₀.B .ldp hlenS).darts.length := by
      rw [selectedGeodesicOfLen_darts, selectedGeodesicOfLen_darts]
    calc
      (selectedGeodesicOfLen R₀.B .ldp hR).darts.length = i :=
        hlenEqR.trans hiLen
      _ ≤ j := hij
      _ = (selectedGeodesicOfLen S₀.B .ldp hS).darts.length :=
        hjLen.symm.trans hlenEqS.symm
  | sdp =>
    obtain ⟨hlenR, hprefixR⟩ := selectedCutRep_recordStage_edgeIds_eq_sdpPrefix
      ht hA hB hfin hL htrans hRbound c hc R₀ I hboundary hgS
    obtain ⟨hlenS, hprefixS⟩ := selectedCutRep_recordStage_edgeIds_eq_sdpPrefix
      ht' hA' hB' hfin hL htrans hRbound c' hc' S₀ J hboundary' hgS
    rcases hprefixR with ⟨i, hiLen, _, hiFirst, _⟩
    rcases hprefixS with ⟨j, hjLen, hjVertex, hjFirst, _⟩
    have hreachQ : Reachable (recordVertex w t)
        ((kmswLeftmostSdpPath w hfin hL htrans hRbound 0 hgS).initial j).1 := by
      rw [hjVertex]
      exact hreach
    have hij := infinitePresentPath_firstVisit_index_le_of_cut hfin hL
      htrans hRbound hcut _ hiFirst hreachQ
    have hlenEqR : (selectedGeodesicOfLen R₀.B .sdp hR).darts.length =
        (selectedGeodesicOfLen R₀.B .sdp hlenR).darts.length := by
      rw [selectedGeodesicOfLen_darts, selectedGeodesicOfLen_darts]
    have hlenEqS : (selectedGeodesicOfLen S₀.B .sdp hS).darts.length =
        (selectedGeodesicOfLen S₀.B .sdp hlenS).darts.length := by
      rw [selectedGeodesicOfLen_darts, selectedGeodesicOfLen_darts]
    calc
      (selectedGeodesicOfLen R₀.B .sdp hR).darts.length = i :=
        hlenEqR.trans hiLen
      _ ≤ j := hij
      _ = (selectedGeodesicOfLen S₀.B .sdp hS).darts.length :=
        hjLen.symm.trans hlenEqS.symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Common-stage edge IDs of two finite path prefixes are ordered by prefix -/
theorem stageDartList_commonInfinitePrefix_edgeIds_prefix
    {w : ℕ → Fin 3} {v n m : ℕ} (hnm : n ≤ m)
    (Q : InfinitePresentPath w ⟨v⟩)
    (ds : List (StageDart (kmswStage w n).nextEdge))
    (es : List (StageDart (kmswStage w m).nextEdge))
    (hlen : ds.length ≤ es.length)
    (hds : ds.map (fun d => d.1.val) =
      List.ofFn (fun i : Fin ds.length => Q.edge i.val))
    (hes : es.map (fun d => d.1.val) =
      List.ofFn (fun i : Fin es.length => Q.edge i.val)) :
    ((ds.map (outerSucc_castDart (kmswStage_nextEdge_mono w hnm))).map
      (fun d => d.1.val)) <+: es.map (fun d => d.1.val) := by
  have hpath : List.ofFn (fun i : Fin ds.length => Q.edge i.val) <+:
      List.ofFn (fun i : Fin es.length => Q.edge i.val) := by
    have h := infinitePresentPath_initial_edgeList_prefix Q hlen
    rw [Q.prefix_edges, Q.prefix_edges] at h
    exact h
  calc
    ((ds.map (outerSucc_castDart (kmswStage_nextEdge_mono w hnm))).map
        (fun d => d.1.val)) = ds.map (fun d => d.1.val) :=
      stageInclusion_dartList_edgeIds hnm ds
    _ = List.ofFn (fun i : Fin ds.length => Q.edge i.val) := hds
    _ <+: List.ofFn (fun i : Fin es.length => Q.edge i.val) := hpath
    _ = es.map (fun d => d.1.val) := hes.symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Selected paths identified with one infinite path form a common-stage prefix. -/
theorem selectedCutRep_commonStage_edgeIds_prefix
    {ℓ r t ℓ' r' t' : ℕ} {w : ℕ → Fin 3} (htt' : t ≤ t')
    (R₀ : KMSWMapRep ℓ r t) (S₀ : KMSWMapRep ℓ' r' t')
    (x : XDP) (d : ℕ) (e : ℕ)
    (hR : xdpLengthBase R₀.B x = d)
    (hS : xdpLengthBase S₀.B x = e)
    (I : DirectedMapWithMissingIso R₀.B.map
      (kmswStageDirectedMap w (t - 1)))
    (J : DirectedMapWithMissingIso S₀.B.map
      (kmswStageDirectedMap w (t' - 1)))
    (Q : InfinitePresentPath w ⟨0⟩)
    (hfirst : ((selectedGeodesicOfLen R₀.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun i : Fin
        (selectedGeodesicOfLen R₀.B x hR).darts.length => Q.edge i.val))
    (hsecond : ((selectedGeodesicOfLen S₀.B x hS).darts.map J.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun i : Fin
        (selectedGeodesicOfLen S₀.B x hS).darts.length => Q.edge i.val))
    (hlen : (selectedGeodesicOfLen R₀.B x hR).darts.length ≤
      (selectedGeodesicOfLen S₀.B x hS).darts.length) :
    ((selectedGeodesicOfLen R₀.B x hR).darts.map
      (outerSucc_castDart (kmswStage_nextEdge_mono w
        (by omega : t - 1 ≤ t' - 1)) ∘ I.toEquiv)).map
        (fun d => d.1.val) <+:
      ((selectedGeodesicOfLen S₀.B x hS).darts.map J.toEquiv).map
        (fun d => d.1.val) := by
  have hstage : t - 1 ≤ t' - 1 := by omega
  have hfirst' :
      (((selectedGeodesicOfLen R₀.B x hR).darts.map I.toEquiv).map
        (fun d => d.1.val)) = List.ofFn (fun i : Fin
          ((selectedGeodesicOfLen R₀.B x hR).darts.map I.toEquiv).length =>
            Q.edge i.val) := by
    rw [List.length_map]
    exact hfirst
  have hsecond' :
      (((selectedGeodesicOfLen S₀.B x hS).darts.map J.toEquiv).map
        (fun d => d.1.val)) = List.ofFn (fun i : Fin
          ((selectedGeodesicOfLen S₀.B x hS).darts.map J.toEquiv).length =>
            Q.edge i.val) := by
    rw [List.length_map]
    exact hsecond
  have hprefix := stageDartList_commonInfinitePrefix_edgeIds_prefix hstage Q
    ((selectedGeodesicOfLen R₀.B x hR).darts.map I.toEquiv)
    ((selectedGeodesicOfLen S₀.B x hS).darts.map J.toEquiv)
    (by simpa only [List.length_map] using hlen) hfirst' hsecond'
  have hmap : ((selectedGeodesicOfLen R₀.B x hR).darts.map
      (outerSucc_castDart (kmswStage_nextEdge_mono w hstage) ∘ I.toEquiv)).map
        (fun d => d.1.val) =
      (((selectedGeodesicOfLen R₀.B x hR).darts.map I.toEquiv).map
        (outerSucc_castDart (kmswStage_nextEdge_mono w hstage))).map
          (fun d => d.1.val) := by
    simp only [List.map_map, Function.comp_def]
  rw [hmap]
  exact hprefix

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An edge-ID prefix between forward stage darts is a dart prefix. -/
theorem stageDartList_edgeIds_prefix_to_darts
    {n : ℕ} {ds es : List (StageDart n)}
    (hids : ds.map (fun d => d.1.val) <+: es.map (fun d => d.1.val))
    (hds : ∀ d ∈ ds, d.2 = false)
    (hes : ∀ d ∈ es, d.2 = false) : ds <+: es := by
  have hlen : ds.length ≤ es.length := by
    simpa only [List.length_map] using hids.length_le
  apply (List.prefix_iff_eq_take).2
  apply List.ext_get
  · simp only [List.length_take, Nat.min_eq_left hlen]
  · intro i hi hiTake
    have hiEs : i < es.length := by omega
    have hval := hids.getElem (i := i) (by
      simpa only [List.length_map] using hi)
    have hval' : (ds[i]'hi).1.val = (es[i]'hiEs).1.val := by
      simpa only [List.getElem_map] using hval
    have hsideD : (ds[i]'hi).2 = false := hds _ (List.getElem_mem hi)
    have hsideE : (es[i]'hiEs).2 = false := hes _ (List.getElem_mem hiEs)
    have hpair : ds[i]'hi = es[i]'hiEs := by
      apply Prod.ext
      · exact Fin.ext hval'
      · exact hsideD.trans hsideE.symm
    simpa only [List.get_eq_getElem, List.getElem_take] using hpair

private theorem stageIsoVertex_source_id {ℓ r n : ℕ} {w : ℕ → Fin 3}
    (R : KMSWMapRep ℓ r n) (k : ℕ)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w k))
    (hb : ∀ a : ThinMapSide, (boundaryDarts R.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w k).UL
          | .right => (kmswStage w k).LR).map (fun e => (e, false))) :
    (stageMapVertex w k (cutMapIsoVertexEquiv I R.B.source)).id = 0 := by
  let d := R.B.rightPath.firstDart (Nat.zero_lt_of_lt R.B.right_length_pos)
  have hpos : 0 < R.B.rightPath.darts.length := by
    rw [R.B.rightPath.darts_length]
    exact Nat.zero_lt_of_lt R.B.right_length_pos
  have hd : R.B.rightPath.darts[0]? = some d := List.getElem?_eq_getElem hpos
  have hLRhead : (kmswStage w k).LR.head? = some 0 := by
    clear hd hpos
    clear d
    clear R I hb
    induction k with
    | zero => rfl
    | succ k ih =>
      change (kmswStepOfStep (kmswStage w k) (kmswCodeStep (w k))).LR.head? = _
      cases kmswCodeStep (w k) with
      | up => exact ih
      | left => simp only [kmswStepOfStep]; split <;> exact ih
      | down =>
        simp only [kmswStepOfStep]
        split
        · exact ih
        · change ((kmswStage w k).LR ++ [(kmswStage w k).nextEdge]).head? = _
          simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w k)]
            using ih
  have hLR : (kmswStage w k).LR[0]? = some 0 := by
    simpa only [List.head?_eq_getElem?] using hLRhead
  have hboundary := hb .right
  simp only [boundaryDarts] at hboundary
  have h := congrArg (fun ds : List (ℕ × Bool) => ds[0]?) hboundary
  simp only [List.getElem?_map, hd, hLR, Option.map_some] at h
  have hpair := Option.some.inj h
  have hindex : (I.toEquiv d).1.val = 0 := congrArg Prod.fst hpair
  have hside : (I.toEquiv d).2 = false := congrArg Prod.snd hpair
  have hsource : R.B.source = dartTailVertex R.B.map d := by
    calc
      R.B.source = R.B.rightPath.vertices.get ⟨0, by
        rw [R.B.rightPath.vertices_length]
        omega⟩ :=
        R.B.rightPath.start_vertex.symm
      _ = dartTailVertex R.B.map d := by
        exact (R.B.rightPath.edge_step ⟨0, hpos⟩).2.2.1
  change (stageMapVertex w k (cutMapIsoVertexEquiv I R.B.source)).id = 0
  rw [hsource, (cutMapIsoVertexEquiv_endpoints I d).1, stageMapVertex_tail]
  unfold stageEndpoint
  rw [hside, hindex]
  exact (initial_edge_endpoints w k).1

private theorem stageIsoVertex_head_id {ℓ r n k : ℕ} {w : ℕ → Fin 3}
    (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w k))
    (d : Fin R.dartCount) (hd : (I.toEquiv d).2 = false) :
    (stageMapVertex w k (cutMapIsoVertexEquiv I (dartHeadVertex R.B.map d))).id =
      edgeEast w (I.toEquiv d).1.val := by
  rw [(cutMapIsoVertexEquiv_endpoints I d).2]
  change (stageMapVertex w k
    (dartTailVertex (kmswStageDirectedMap w k)
      ((kmswStageDirectedMap w k).edgeInv (I.toEquiv d)))).id = _
  rw [stageMapVertex_tail]
  change (if !((I.toEquiv d).2) then
    (kmswStage w k).east (I.toEquiv d).1.val else
    (kmswStage w k).west (I.toEquiv d).1.val) = _
  rw [hd]
  exact (edge_endpoints_eq w (I.toEquiv d).1.isLt).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The two record-stage selected geodesics agree as a common selected prefix. -/
theorem selectedCutRep_commonSelectedPrefix
    {ℓ r t ℓ' r' t' m m' : ℕ} {w : ℕ → Fin 3}
    (htt' : t ≤ t') (ht : 1 ≤ t) (ht' : 1 ≤ t')
    (hA : ∀ j < t, R w t ≤ R w j - 1)
    (hB : ∀ j, t ≤ j → L w t ≤ L w j)
    (hA' : ∀ j < t', R w t' ≤ R w j - 1)
    (hB' : ∀ j, t' ≤ j → L w t' ≤ L w j)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hRbound : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (c : KMSWWalkClass ℓ r t)
    (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R₀ : KMSWMapRep ℓ r t)
    (I : DirectedMapWithMissingIso R₀.B.map
      (kmswStageDirectedMap w (t - 1)))
    (hboundary : ∀ a : ThinMapSide, (boundaryDarts R₀.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false)))
    (c' : KMSWWalkClass ℓ' r' t')
    (hc' : ∀ i < t' - 1, codeExtend c' i = w i)
    (S₀ : KMSWMapRep ℓ' r' t')
    (J : DirectedMapWithMissingIso S₀.B.map
      (kmswStageDirectedMap w (t' - 1)))
    (hboundary' : ∀ a : ThinMapSide, (boundaryDarts S₀.B a).map
      (fun d => ((J.toEquiv d).1.val, (J.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t' - 1)).UL
          | .right => (kmswStage w (t' - 1)).LR).map (fun e => (e, false)))
    (x : XDP) (hR : xdpLengthBase R₀.B x = m)
    (hS : xdpLengthBase S₀.B x = m')
    (hgL : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments)
    (hgS : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    CommonSelectedPrefix R₀ hR S₀ hS
      (outerSucc_castDart
        (kmswStage_nextEdge_mono w (Nat.sub_le_sub_right htt' 1)) ∘ I.toEquiv)
      J.toEquiv
      (fun u => (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I u)).id)
      (fun u => (stageMapVertex w (t' - 1) (cutMapIsoVertexEquiv J u)).id) := by
  let hstage : t - 1 ≤ t' - 1 := Nat.sub_le_sub_right htt' 1
  let fd := outerSucc_castDart (kmswStage_nextEdge_mono w hstage) ∘ I.toEquiv
  let gd := J.toEquiv
  let fv := fun u => (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I u)).id
  let gv := fun u => (stageMapVertex w (t' - 1) (cutMapIsoVertexEquiv J u)).id
  let PR := selectedGeodesicOfLen R₀.B x hR
  let PS := selectedGeodesicOfLen S₀.B x hS
  let Q : InfinitePresentPath w ⟨0⟩ := match x with
    | .ldp => kmswLeftmostLdpPath w hfin hL htrans hRbound 0 hgL
    | .sdp => kmswLeftmostSdpPath w hfin hL htrans hRbound 0 hgS
  have hlen := selectedCutRep_recordStage_dartLength_le htt' ht ht'
    hA hB hA' hB' hfin hL htrans hRbound c hc R₀ I hboundary
    c' hc' S₀ J hboundary' x hR hS hgL hgS
  have hfirst : ((PR.darts.map I.toEquiv).map (fun d => d.1.val)) =
      List.ofFn (fun i : Fin PR.darts.length => Q.edge i.val) := by
    cases x with
    | ldp =>
      obtain ⟨hlenR, hprefix⟩ := selectedCutRep_recordStage_edgeIds_eq_ldpPrefix
        ht hA hB hfin hL htrans hRbound c hc R₀ I hboundary hgL
      rcases hprefix with ⟨i, hi, _, _, hids⟩
      let P₀ := selectedGeodesicOfLen R₀.B .ldp hlenR
      have hlength : P₀.darts.length = PR.darts.length := by
        simp only [P₀, PR, selectedGeodesicOfLen_darts]
      have hcast : List.ofFn (fun j : Fin P₀.darts.length => Q.edge j.val) =
          List.ofFn (fun j : Fin PR.darts.length => Q.edge j.val) := by
        rw [List.ofFn_congr hlength]
        simp only [Fin.val_cast]
      simpa only [P₀, PR, Q, selectedGeodesicOfLen_darts] using hids.trans hcast
    | sdp =>
      obtain ⟨hlenR, hprefix⟩ := selectedCutRep_recordStage_edgeIds_eq_sdpPrefix
        ht hA hB hfin hL htrans hRbound c hc R₀ I hboundary hgS
      rcases hprefix with ⟨i, hi, _, _, hids⟩
      let P₀ := selectedGeodesicOfLen R₀.B .sdp hlenR
      have hlength : P₀.darts.length = PR.darts.length := by
        simp only [P₀, PR, selectedGeodesicOfLen_darts]
      have hcast : List.ofFn (fun j : Fin P₀.darts.length => Q.edge j.val) =
          List.ofFn (fun j : Fin PR.darts.length => Q.edge j.val) := by
        rw [List.ofFn_congr hlength]
        simp only [Fin.val_cast]
      simpa only [P₀, PR, Q, selectedGeodesicOfLen_darts] using hids.trans hcast
  have hsecond : ((PS.darts.map J.toEquiv).map (fun d => d.1.val)) =
      List.ofFn (fun i : Fin PS.darts.length => Q.edge i.val) := by
    cases x with
    | ldp =>
      obtain ⟨hlenS, hprefix⟩ := selectedCutRep_recordStage_edgeIds_eq_ldpPrefix
        ht' hA' hB' hfin hL htrans hRbound c' hc' S₀ J hboundary' hgL
      rcases hprefix with ⟨i, hi, _, _, hids⟩
      let P₀ := selectedGeodesicOfLen S₀.B .ldp hlenS
      have hlength : P₀.darts.length = PS.darts.length := by
        simp only [P₀, PS, selectedGeodesicOfLen_darts]
      have hcast : List.ofFn (fun j : Fin P₀.darts.length => Q.edge j.val) =
          List.ofFn (fun j : Fin PS.darts.length => Q.edge j.val) := by
        rw [List.ofFn_congr hlength]
        simp only [Fin.val_cast]
      simpa only [P₀, PS, Q, selectedGeodesicOfLen_darts] using hids.trans hcast
    | sdp =>
      obtain ⟨hlenS, hprefix⟩ := selectedCutRep_recordStage_edgeIds_eq_sdpPrefix
        ht' hA' hB' hfin hL htrans hRbound c' hc' S₀ J hboundary' hgS
      rcases hprefix with ⟨i, hi, _, _, hids⟩
      let P₀ := selectedGeodesicOfLen S₀.B .sdp hlenS
      have hlength : P₀.darts.length = PS.darts.length := by
        simp only [P₀, PS, selectedGeodesicOfLen_darts]
      have hcast : List.ofFn (fun j : Fin P₀.darts.length => Q.edge j.val) =
          List.ofFn (fun j : Fin PS.darts.length => Q.edge j.val) := by
        rw [List.ofFn_congr hlength]
        simp only [Fin.val_cast]
      simpa only [P₀, PS, Q, selectedGeodesicOfLen_darts] using hids.trans hcast
  have hids := selectedCutRep_commonStage_edgeIds_prefix htt' R₀ S₀ x m m'
    hR hS I J Q hfirst hsecond (by simpa only [PR, PS] using hlen)
  have hDarts : PR.darts.map fd <+: PS.darts.map gd := by
    apply stageDartList_edgeIds_prefix_to_darts hids
    · intro d hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      rw [Function.comp_apply]
      rw [stageInclusion_dart_side hstage]
      exact directedPath_stageIso_darts_forward I
        (selectedGeodesicOfLen R₀.B x hR) e he
    · intro d hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      exact directedPath_stageIso_darts_forward J
        (selectedGeodesicOfLen S₀.B x hS) e he
  have hrootR := stageIsoVertex_source_id R₀ (t - 1) I hboundary
  have hrootS := stageIsoVertex_source_id S₀ (t' - 1) J hboundary'
  have hlength : m ≤ m' := by
    calc
      m = PR.darts.length := PR.darts_length.symm
      _ ≤ PS.darts.length := hlen
      _ = m' := PS.darts_length
  refine ⟨?_, ?_, ?_⟩
  · exact hlength
  · intro i hi
    have hiR : i < PR.darts.length := by rw [PR.darts_length]; exact hi
    have hiS : i < PS.darts.length := by
      rw [PS.darts_length]
      exact lt_of_lt_of_le hi hlength
    let e := PR.darts.get ⟨i, hiR⟩
    let e' := PS.darts.get ⟨i, hiS⟩
    have heq : fd e = gd e' := by
      have h := hDarts.getElem (i := i)
        (by simpa only [List.length_map] using hiR)
      simpa only [List.getElem_map, List.get_eq_getElem, e, e', fd, gd] using h
    refine ⟨e, e', ?_, ?_, heq⟩
    · exact List.getElem?_eq_getElem hiR
    · exact List.getElem?_eq_getElem hiS
  · intro i hi
    have hivR : i < PR.vertices.length := by
      rw [PR.vertices_length]
      omega
    have hivS : i < PS.vertices.length := by
      rw [PS.vertices_length]
      omega
    let u := PR.vertices.get ⟨i, hivR⟩
    let u' := PS.vertices.get ⟨i, hivS⟩
    have hvertex : fv u = gv u' := by
      cases i with
      | zero =>
        dsimp only [fv, gv, u, u']
        rw [PR.start_vertex, PS.start_vertex]
        exact hrootR.trans hrootS.symm
      | succ j =>
        have hj : j < m := by omega
        have hjR : j < PR.darts.length := by rw [PR.darts_length]; exact hj
        have hjS : j < PS.darts.length := by
          rw [PS.darts_length]
          exact lt_of_lt_of_le hj hlength
        let e := PR.darts.get ⟨j, hjR⟩
        let e' := PS.darts.get ⟨j, hjS⟩
        have heq : fd e = gd e' := by
          have h := hDarts.getElem (i := j)
            (by simpa only [List.length_map] using hjR)
          simpa only [List.getElem_map, List.get_eq_getElem, e, e', fd, gd] using h
        have hval : (I.toEquiv e).1.val = (J.toEquiv e').1.val := by
          have h := congrArg (fun d : StageDart (kmswStage w (t' - 1)).nextEdge =>
            d.1.val) heq
          simpa [fd, gd, outerSucc_castDart] using h
        have hforwardR := directedPath_stageIso_darts_forward I
          (selectedGeodesicOfLen R₀.B x hR) e (List.get_mem _ _)
        have hforwardS := directedPath_stageIso_darts_forward J
          (selectedGeodesicOfLen S₀.B x hS) e' (List.get_mem _ _)
        have hheadR := stageIsoVertex_head_id R₀ I e hforwardR
        have hheadS := stageIsoVertex_head_id S₀ J e' hforwardS
        have hheads :
            (stageMapVertex w (t - 1)
              (cutMapIsoVertexEquiv I (dartHeadVertex R₀.B.map e))).id =
            (stageMapVertex w (t' - 1)
              (cutMapIsoVertexEquiv J (dartHeadVertex S₀.B.map e'))).id := by
          rw [hheadR, hheadS, hval]
        have hstepR := PR.edge_step ⟨j, hjR⟩
        have hstepS := PS.edge_step ⟨j, hjS⟩
        dsimp only [fv, gv, u, u']
        rw [hstepR.2.2.2, hstepS.2.2.2]
        exact hheads
    refine ⟨u, u', ?_, ?_, hvertex⟩
    · exact List.getElem?_eq_getElem hivR
    · exact List.getElem?_eq_getElem hivS

/-! The first record-stage edge-ID bridge is proved for both LDP and SDP. The second-cut
SDP bridge is the same theorem at `t'`. `selectedCutRep_commonStage_edgeIds_prefix`
orders two selected paths after stage inclusion when both edge lists agree with the
same infinite path and the first selected path has no more darts than the second.

To apply these results to a concrete pair from
`selectedCutPastCuts_representatives_record_stageIso`, provide the two record-condition
pairs `hA`/`hB` and `hA'`/`hB'`, the resulting edge-ID equalities for the same chosen
leftmost path, and the selected-path length inequality. The latter three are the exact
inputs `hfirst`, `hsecond`, and `hlen` of
`selectedCutRep_commonStage_edgeIds_prefix`; obtaining the length inequality from the
concrete cut witnesses is outside this file's current declarations. -/

end DirectedDistances.PaperProofs.Section4
