module

public import DirectedDistances.PaperProofs.Section5.GeoInftyIdentified
public import DirectedDistances.PaperProofs.Section1.BusemannM0Identified

/-! # Busemann increment from coalescing infinite geodesics

Deterministic helpers toward Lemma 5.7 (`lem-busemann-cls`,
the Lean edge stream is zero-based, so source edge `t` is Lean edge `t - 1`. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver DirectedDistances.KMSW DirectedDistances.PaperProofs.Section1

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- For source edges numbered `t ≥ 1`, Lean index `n = t - 1` compares edges
`theta + n` and `theta' + n`; equality retains the whole-plane edge identity. -/
@[expose] def M0CutEdgeTailsCoalesce {k k' : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (P' : M0CutInfiniteGeodesic W H h hLL k' longest)
    (theta theta' : ℕ) : Prop :=
  ∀ n : ℕ, wholePlaneEdgeι W 0 (P.codePath.edge (theta + n)) =
    wholePlaneEdgeι W 0 (P'.codePath.edge (theta' + n))

/-- The source's least coalescing indices in `eqn-coalesce`
streams. The second clause records that both offsets are least among aligned
coalescing tails. -/
@[expose] def M0CutLeastEdgeCoalescence {k k' : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (P' : M0CutInfiniteGeodesic W H h hLL k' longest)
    (theta theta' : ℕ) : Prop :=
  M0CutEdgeTailsCoalesce P P' theta theta' ∧
    ∀ a b : ℕ, M0CutEdgeTailsCoalesce P P' a b → theta ≤ a ∧ theta' ≤ b

private theorem presentVertex_eq_of_id_eq {w : ℕ → Fin 3}
    {u v : PresentVertex w} (h : u.id = v.id) : u = v := by
  cases u with
  | mk u =>
    cases v with
    | mk v =>
      simp only at h
      subst v
      rfl

/-- A present infinite path cannot revisit an earlier vertex, since the
intervening segment would be a directed cycle -/
private theorem path_initial_vertex_ne_of_lt {w : ℕ → Fin 3}
    {x : PresentVertex w} (P : InfinitePresentPath w x) {i j : ℕ}
    (hij : i < j) : (P.initial i).1 ≠ (P.initial j).1 := by
  intro heq
  let p := (P.initial j).2
  have hpLen : p.length = j := P.prefix_length j
  obtain ⟨z, p₁, p₂, hp, hp₁⟩ :=
    p.exists_eq_comp_of_le_length (n := i) (by omega)
  have hfull : pathEdgeList p₁ ++ pathEdgeList p₂ =
      List.ofFn (fun n : Fin j => P.edge n.val) := by
    rw [← pathEdgeList_comp, ← hp, P.prefix_edges]
  let full : List ℕ := List.ofFn (fun n : Fin j => P.edge n.val)
  have hsplit : full.take i ++ full.drop i = full := List.take_append_drop i full
  have hconcat : pathEdgeList p₁ ++ pathEdgeList p₂ =
      full.take i ++ full.drop i := by
    calc
      pathEdgeList p₁ ++ pathEdgeList p₂ = full := by simpa [full] using hfull
      _ = full.take i ++ full.drop i := hsplit.symm
  have htake : pathEdgeList p₁ = full.take i :=
    List.append_inj_left hconcat (by
      rw [pathEdgeList_length, hp₁, List.length_take]
      simp [full, Nat.min_eq_left (Nat.le_of_lt hij)])
  have hprefix : List.ofFn (fun n : Fin i => P.edge n.val) = full.take i := by
    apply List.ext_get
    · simp [full, Nat.min_eq_left (Nat.le_of_lt hij)]
    · intro n hn₁ hn₂
      simp [full, List.get_eq_getElem]
  have hz : z.id = (P.initial i).1.id := by
    have hp₁end := pathEdgeList_endpoint p₁
    have hinitial := pathEdgeList_endpoint (P.initial i).2
    rw [P.prefix_edges] at hinitial
    rw [htake, ← hprefix] at hp₁end
    exact hp₁end.symm.trans hinitial
  let q := p₁.comp p₂
  have hqLen : q.length = j := (congrArg Path.length hp).symm.trans hpLen
  have hqi : i < q.vertices.length := by
    rw [Path.vertices_length, hqLen]
    omega
  have hqj : j < q.vertices.length := by
    rw [Path.vertices_length, hqLen]
    omega
  have hvertex : q.vertices.get ⟨i, hqi⟩ = (P.initial i).1 := by
    have hz' := Path.vertices_comp_get_length_eq p₁ p₂
    have hz'' : q.vertices.get ⟨i, hqi⟩ = z := by
      have hp₁bound : p₁.length < q.vertices.length := by
        have hi : i < q.vertices.length := hqi
        omega
      have hidx : (⟨i, hqi⟩ : Fin q.vertices.length) =
          ⟨p₁.length, hp₁bound⟩ := by
        apply Fin.ext
        exact hp₁.symm
      rw [hidx]
      exact hz'
    exact hz''.trans (presentVertex_eq_of_id_eq hz)
  have hlast : q.vertices.get ⟨j, hqj⟩ = (P.initial j).1 := by
    have hlenSub : q.vertices.length - 1 < q.vertices.length := by
      rw [Path.vertices_length, hqLen]
      omega
    have hget := List.get_length_sub_one hlenSub
    have hend := Path.vertices_getLast q q.vertices_ne_nil
    rw [hend] at hget
    have hidx : (⟨q.vertices.length - 1, hlenSub⟩ : Fin q.vertices.length) =
        ⟨j, hqj⟩ := by
      have hval : q.vertices.length - 1 = j := by
        have hlen : q.vertices.length = j + 1 := by
          rw [Path.vertices_length, hqLen]
        omega
      apply Fin.ext
      exact hval
    rw [hidx] at hget
    exact hget
  have hsame : q.vertices.get ⟨i, hqi⟩ = q.vertices.get ⟨j, hqj⟩ :=
    hvertex.trans (heq.trans hlast.symm)
  have hidx := (List.Nodup.get_inj_iff
    (vertices_nodup_of_acyclic (presentVertex_acyclic w) q)).mp hsame
  have hval : i = j := congrArg Fin.val hidx
  exact (Nat.ne_of_lt hij) hval

/-- Vertices along a present infinite path are pairwise distinct by acyclicity -/
private theorem path_initial_vertices_injective {w : ℕ → Fin 3}
    {x : PresentVertex w} (P : InfinitePresentPath w x) :
    Function.Injective (fun n => (P.initial n).1) := by
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    exact path_initial_vertex_ne_of_lt P hlt hij
  · exact heq
  · exfalso
    exact path_initial_vertex_ne_of_lt P hgt hij.symm

/-- Equal edge tails have equal vertices at the starts of their corresponding -/
theorem m0Cut_coalesced_initial_eq {k k' : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (P' : M0CutInfiniteGeodesic W H h hLL k' longest)
    (theta theta' j : ℕ)
    (hco : M0CutEdgeTailsCoalesce P P' theta theta') :
    (P.codePath.initial (theta + j)).1 =
      (P'.codePath.initial (theta' + j)).1 := by
  have he : P.codePath.edge (theta + j) = P'.codePath.edge (theta' + j) :=
    wholePlaneEdgeι_injective W 0 (hco j)
  have hleft := P.codePath.edge_outgoing_at_initial (shiftedStream W 0) (theta + j)
  have hright := P'.codePath.edge_outgoing_at_initial (shiftedStream W 0) (theta' + j)
  apply presentVertex_eq_of_id_eq
  calc
    (P.codePath.initial (theta + j)).1.id =
        edgeWest (shiftedStream W 0) (P.codePath.edge (theta + j)) := hleft.2.symm
    _ = edgeWest (shiftedStream W 0) (P'.codePath.edge (theta' + j)) := by rw [he]
    _ = (P'.codePath.initial (theta' + j)).1.id := hright.2

/-- Every vertex on the identified image of a cut geodesic is reachable from -/
private theorem m0Cut_path_vertex_reachable {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ) :
    m0CutReachable W H (m0CutData W H h hLL).seam
      ((m0CutData W H h hLL).x k)
      (wholePlaneVertexι W 0 ((P.codePath.initial n).1.id)) := by
  rw [P.startsAtCutBoundary]
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, ?_⟩
    exact ⟨wholePlaneVertexι W 0 ((P.codePath.initial n).1.id), hm, P.cutStep n⟩

/-- A finite prefix of an XDP path realizes its finite LDP distance -/
theorem m0Cut_ldp_prefix_distance {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k true) (n : ℕ) :
    (m0CutData W H h hLL).ldp ((m0CutData W H h hLL).x k)
      (wholePlaneVertexι W 0 ((P.codePath.initial n).1.id)) =
        (((n : ℕ∞) : WithBot ℕ∞)) := by
  let w := shiftedStream W 0
  have hstart0 : boundaryPresentVertex w h k = (P.codePath.initial 0).1 :=
    (P.codePath.initial 0).2.eq_of_length_zero (P.codePath.prefix_length 0)
  have hstart : (m0CutData W H h hLL).x k =
      wholePlaneVertexι W 0 (boundaryVertex w h k) := by
    calc
      (m0CutData W H h hLL).x k =
          wholePlaneVertexι W 0 ((P.codePath.initial 0).1.id) := P.startsAtCutBoundary
      _ = wholePlaneVertexι W 0 (boundaryVertex w h k) := by
        congr 1
        exact congrArg PresentVertex.id hstart0.symm
  have hsource : (⟨boundaryVertex w h k⟩ : PresentVertex w) =
      boundaryPresentVertex w h k := presentVertex_eq_of_id_eq rfl
  have htarget : (⟨(P.codePath.initial n).1.id⟩ : PresentVertex w) =
      (P.codePath.initial n).1 := presentVertex_eq_of_id_eq rfl
  have hopt := P.codePath.initial_isLongest w P.segments n
  change m0CutLDP W H (m0CutData W H h hLL).seam
    ((m0CutData W H h hLL).x k)
    (wholePlaneVertexι W 0 ((P.codePath.initial n).1.id)) = _
  rw [hstart]
  calc
    m0CutLDP W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 (boundaryVertex w h k))
        (wholePlaneVertexι W 0 ((P.codePath.initial n).1.id)) =
      presentLdp (⟨boundaryVertex w h k⟩ : PresentVertex w)
        ⟨(P.codePath.initial n).1.id⟩ :=
          m0Cut_ldp_eq_present W H h hLL (m0CutData W H h hLL).seam
            (m0Cut_seamEdge_iff W H h hLL)
            (boundaryVertex w h k) (P.codePath.initial n).1.id
    _ = presentLdp (boundaryPresentVertex w h k) (P.codePath.initial n).1 := by
      rw [hsource, htarget]
    _ = (((((P.codePath.initial n).2.length : ℕ∞) : WithBot ℕ∞))) :=
      presentLdp_eq_length hopt
    _ = (((n : ℕ∞) : WithBot ℕ∞)) := by rw [P.codePath.prefix_length]

/-- A finite prefix of an SDP path realizes its finite SDP distance -/
theorem m0Cut_sdp_prefix_distance {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k false) (n : ℕ) :
    (m0CutData W H h hLL).sdp ((m0CutData W H h hLL).x k)
      (wholePlaneVertexι W 0 ((P.codePath.initial n).1.id)) =
        (n : ℕ∞) := by
  let w := shiftedStream W 0
  have hstart0 : boundaryPresentVertex w h k = (P.codePath.initial 0).1 :=
    (P.codePath.initial 0).2.eq_of_length_zero (P.codePath.prefix_length 0)
  have hstart : (m0CutData W H h hLL).x k =
      wholePlaneVertexι W 0 (boundaryVertex w h k) := by
    calc
      (m0CutData W H h hLL).x k =
          wholePlaneVertexι W 0 ((P.codePath.initial 0).1.id) := P.startsAtCutBoundary
      _ = wholePlaneVertexι W 0 (boundaryVertex w h k) := by
        congr 1
        exact congrArg PresentVertex.id hstart0.symm
  have hsource : (⟨boundaryVertex w h k⟩ : PresentVertex w) =
      boundaryPresentVertex w h k := presentVertex_eq_of_id_eq rfl
  have htarget : (⟨(P.codePath.initial n).1.id⟩ : PresentVertex w) =
      (P.codePath.initial n).1 := presentVertex_eq_of_id_eq rfl
  have hopt := P.codePath.initial_isShortest w P.segments n
  change m0CutSDP W H (m0CutData W H h hLL).seam
    ((m0CutData W H h hLL).x k)
    (wholePlaneVertexι W 0 ((P.codePath.initial n).1.id)) = _
  rw [hstart]
  calc
    m0CutSDP W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 (boundaryVertex w h k))
        (wholePlaneVertexι W 0 ((P.codePath.initial n).1.id)) =
      sdp (⟨boundaryVertex w h k⟩ : PresentVertex w)
        ⟨(P.codePath.initial n).1.id⟩ :=
          m0Cut_sdp_eq_present W H h hLL (m0CutData W H h hLL).seam
            (m0Cut_seamEdge_iff W H h hLL)
            (boundaryVertex w h k) (P.codePath.initial n).1.id
    _ = sdp (boundaryPresentVertex w h k) (P.codePath.initial n).1 := by
      rw [hsource, htarget]
    _ = (n : ℕ∞) := by
      have hoptDist := ((isShortest_iff_length_eq_sdp _).1 hopt).symm
      have hlenCast : ((P.codePath.initial n).2.length : ℕ∞) = n :=
        congrArg (fun m : ℕ => (m : ℕ∞)) (P.codePath.prefix_length n)
      have hsourceDist := congrArg
        (fun z : PresentVertex w => sdp z (P.codePath.initial n).1) hsource
      exact hsourceDist.symm.trans (by simpa only [w] using hoptDist.trans hlenCast)

/-- A shifted XDP segment realizes its length as a finite LDP distance -/
private theorem m0Cut_ldp_segment_distance {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k true) (i n : ℕ) :
    m0CutLDP W H (m0CutData W H h hLL).seam
      (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id))
      (wholePlaneVertexι W 0 ((P.codePath.initial (i + n)).1.id)) =
        (((n : ℕ∞) : WithBot ℕ∞)) := by
  let Q := P.codePath.shift i
  have hQ := P.codePath.shift_hasLongestSegments P.segments i
  have hopt := Q.initial_isLongest (shiftedStream W 0) hQ n
  have hqend : (Q.initial n).1 = (P.codePath.initial (i + n)).1 := rfl
  have hsource : (⟨(P.codePath.initial i).1.id⟩ : PresentVertex (shiftedStream W 0)) =
      (P.codePath.initial i).1 := presentVertex_eq_of_id_eq rfl
  have htarget : (⟨(Q.initial n).1.id⟩ : PresentVertex (shiftedStream W 0)) =
      (Q.initial n).1 := presentVertex_eq_of_id_eq rfl
  calc
    m0CutLDP W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id))
        (wholePlaneVertexι W 0 ((P.codePath.initial (i + n)).1.id)) =
      m0CutLDP W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id))
        (wholePlaneVertexι W 0 ((Q.initial n).1.id)) := by rw [← hqend]
    _ =
      presentLdp (⟨(P.codePath.initial i).1.id⟩ : PresentVertex (shiftedStream W 0))
        ⟨(Q.initial n).1.id⟩ :=
          m0Cut_ldp_eq_present W H h hLL (m0CutData W H h hLL).seam
            (m0Cut_seamEdge_iff W H h hLL)
            (P.codePath.initial i).1.id (Q.initial n).1.id
    _ = presentLdp (P.codePath.initial i).1 (Q.initial n).1 := by
      rw [hsource, htarget]
    _ = (((((Q.initial n).2.length : ℕ∞) : WithBot ℕ∞))) :=
      presentLdp_eq_length hopt
    _ = (((n : ℕ∞) : WithBot ℕ∞)) := by rw [Q.prefix_length]

/-- A shifted SDP segment realizes its length as a finite SDP distance -/
private theorem m0Cut_sdp_segment_distance {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k false) (i n : ℕ) :
    m0CutSDP W H (m0CutData W H h hLL).seam
      (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id))
      (wholePlaneVertexι W 0 ((P.codePath.initial (i + n)).1.id)) = (n : ℕ∞) := by
  let Q := P.codePath.shift i
  have hQ := P.codePath.shift_hasShortestSegments P.segments i
  have hopt := Q.initial_isShortest (shiftedStream W 0) hQ n
  have hqend : (Q.initial n).1 = (P.codePath.initial (i + n)).1 := rfl
  have hsource : (⟨(P.codePath.initial i).1.id⟩ : PresentVertex (shiftedStream W 0)) =
      (P.codePath.initial i).1 := presentVertex_eq_of_id_eq rfl
  have htarget : (⟨(Q.initial n).1.id⟩ : PresentVertex (shiftedStream W 0)) =
      (Q.initial n).1 := presentVertex_eq_of_id_eq rfl
  calc
    m0CutSDP W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id))
        (wholePlaneVertexι W 0 ((P.codePath.initial (i + n)).1.id)) =
      m0CutSDP W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id))
        (wholePlaneVertexι W 0 ((Q.initial n).1.id)) := by rw [← hqend]
    _ =
      sdp (⟨(P.codePath.initial i).1.id⟩ : PresentVertex (shiftedStream W 0))
        ⟨(Q.initial n).1.id⟩ :=
          m0Cut_sdp_eq_present W H h hLL (m0CutData W H h hLL).seam
            (m0Cut_seamEdge_iff W H h hLL)
            (P.codePath.initial i).1.id (Q.initial n).1.id
    _ = sdp (P.codePath.initial i).1 (Q.initial n).1 := by
      rw [hsource, htarget]
    _ = (n : ℕ∞) := by
      have hoptDist := ((isShortest_iff_length_eq_sdp _).1 hopt).symm
      have hlenCast : ((Q.initial n).2.length : ℕ∞) = n :=
        congrArg (fun m : ℕ => (m : ℕ∞)) (Q.prefix_length n)
      have hsourceDist := congrArg
        (fun z : PresentVertex (shiftedStream W 0) => sdp z (Q.initial n).1) hsource
      exact hsourceDist.symm.trans (hoptDist.trans hlenCast)

/-- LDP additivity along a geodesic tail, with both summands finite -/
theorem m0Cut_ldp_additive_along_geodesic {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k true) (i n : ℕ) :
    (m0CutData W H h hLL).ldp ((m0CutData W H h hLL).x k)
        (wholePlaneVertexι W 0 ((P.codePath.initial (i + n)).1.id)) =
      (m0CutData W H h hLL).ldp ((m0CutData W H h hLL).x k)
        (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id)) +
      m0CutLDP W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id))
        (wholePlaneVertexι W 0 ((P.codePath.initial (i + n)).1.id)) := by
  rw [m0Cut_ldp_prefix_distance P (i + n), m0Cut_ldp_prefix_distance P i]
  rw [m0Cut_ldp_segment_distance P i n]
  norm_num

/-- SDP additivity along a geodesic tail -/
theorem m0Cut_sdp_additive_along_geodesic {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k false) (i n : ℕ) :
    (m0CutData W H h hLL).sdp ((m0CutData W H h hLL).x k)
        (wholePlaneVertexι W 0 ((P.codePath.initial (i + n)).1.id)) =
      (m0CutData W H h hLL).sdp ((m0CutData W H h hLL).x k)
        (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id)) +
      m0CutSDP W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 ((P.codePath.initial i).1.id))
        (wholePlaneVertexι W 0 ((P.codePath.initial (i + n)).1.id)) := by
  rw [m0Cut_sdp_prefix_distance P (i + n), m0Cut_sdp_prefix_distance P i]
  rw [m0Cut_sdp_segment_distance P i n]
  norm_num

/-- Lemma 5.7's coalescing-geodesic increment identity
The coalescence input is the exact zero-based edge-stream translation: source
edge `t ≥ 1` is Lean edge `t - 1`. -/
theorem m0Cut_busemann_cls_identity {k : ℤ} (longest : Bool)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (P' : M0CutInfiniteGeodesic W H h hLL (k - 1) longest)
    (theta theta' : ℕ)
    (hco : M0CutLeastEdgeCoalescence P P' theta theta')
    (X : ℤ → ℤ)
    (hX : if longest then
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X else
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) :
    X k - X (k - 1) = (theta : ℤ) - (theta' : ℤ) := by
  let V := wholePlaneVertexι W 0
  let y : ℕ → WholePlaneVertex W := fun j =>
    V ((P.codePath.initial (theta + j)).1.id)
  have htail := hco.1
  have hvertex (j : ℕ) :
      (P.codePath.initial (theta + j)).1 =
        (P'.codePath.initial (theta' + j)).1 :=
    m0Cut_coalesced_initial_eq P P' theta theta' j htail
  have hy : Function.Injective y := by
    intro i j hij
    have hids := wholePlaneVertexι_injective W 0 (by simpa [y, V] using hij)
    have hv := presentVertex_eq_of_id_eq hids
    have hidx := path_initial_vertices_injective P.codePath hv
    omega
  have hyr (j : ℕ) :
      m0CutReachable W H (m0CutData W H h hLL).seam
          ((m0CutData W H h hLL).x (k - 1)) (y j) ∧
      m0CutReachable W H (m0CutData W H h hLL).seam
          ((m0CutData W H h hLL).x k) (y j) := by
    constructor
    · have hr := m0Cut_path_vertex_reachable P' (theta' + j)
      change m0CutReachable W H (m0CutData W H h hLL).seam
        ((m0CutData W H h hLL).x (k - 1))
        (V ((P'.codePath.initial (theta' + j)).1.id)) at hr
      have hV : V ((P.codePath.initial (theta + j)).1.id) =
          V ((P'.codePath.initial (theta' + j)).1.id) :=
        congrArg (fun z : PresentVertex (shiftedStream W 0) => V z.id) (hvertex j)
      rw [← hV] at hr
      simpa only [y] using hr
    · have hr := m0Cut_path_vertex_reachable P (theta + j)
      change m0CutReachable W H (m0CutData W H h hLL).seam
        ((m0CutData W H h hLL).x k)
        (V ((P.codePath.initial (theta + j)).1.id)) at hr
      simpa only [y] using hr
  cases longest with
  | false =>
    have hX' : IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X := by
      simpa using hX
    obtain ⟨N, hN⟩ := hX'.2 (k - 1) k y hy hyr
    have hd := hN N le_rfl
    have hdist :
        (m0CutData W H h hLL).sdp ((m0CutData W H h hLL).x k) (y N) = theta + N := by
      simpa [y, V] using m0Cut_sdp_prefix_distance P (theta + N)
    have hdist' :
        (m0CutData W H h hLL).sdp ((m0CutData W H h hLL).x (k - 1)) (y N) = theta' + N := by
      have hV : V ((P.codePath.initial (theta + N)).1.id) =
          V ((P'.codePath.initial (theta' + N)).1.id) :=
        congrArg (fun z : PresentVertex (shiftedStream W 0) => V z.id) (hvertex N)
      have hV' : wholePlaneVertexι W 0 ((P.codePath.initial (theta + N)).1.id) =
          wholePlaneVertexι W 0 ((P'.codePath.initial (theta' + N)).1.id) := hV
      change (m0CutData W H h hLL).sdp ((m0CutData W H h hLL).x (k - 1))
        (wholePlaneVertexι W 0 ((P.codePath.initial (theta + N)).1.id)) = _
      rw [hV']
      exact m0Cut_sdp_prefix_distance P' (theta' + N)
    rw [hdist, hdist'] at hd
    rw [← ENat.natCast_add, ← ENat.natCast_add] at hd
    simp only [ENat.toNat_natCast] at hd
    omega
  | true =>
    have hX' : IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X := by
      simpa using hX
    obtain ⟨N, hN⟩ := hX'.2 (k - 1) k y hy hyr
    obtain ⟨n, n', hdn, hdn', hxd⟩ := hN N le_rfl
    have hdist :
        (m0CutData W H h hLL).ldp ((m0CutData W H h hLL).x k) (y N) =
          (((theta + N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa only [y, V] using m0Cut_ldp_prefix_distance P (theta + N)
    have hdist' :
        (m0CutData W H h hLL).ldp ((m0CutData W H h hLL).x (k - 1)) (y N) =
          (((theta' + N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      have hV : V ((P.codePath.initial (theta + N)).1.id) =
          V ((P'.codePath.initial (theta' + N)).1.id) :=
        congrArg (fun z : PresentVertex (shiftedStream W 0) => V z.id) (hvertex N)
      have hV' : wholePlaneVertexι W 0 ((P.codePath.initial (theta + N)).1.id) =
          wholePlaneVertexι W 0 ((P'.codePath.initial (theta' + N)).1.id) := hV
      change (m0CutData W H h hLL).ldp ((m0CutData W H h hLL).x (k - 1))
        (wholePlaneVertexι W 0 ((P.codePath.initial (theta + N)).1.id)) = _
      rw [hV']
      exact m0Cut_ldp_prefix_distance P' (theta' + N)
    have hn : n = theta + N := by exact_mod_cast hdn.symm.trans hdist
    have hn' : n' = theta' + N := by exact_mod_cast hdn'.symm.trans hdist'
    rw [hn, hn'] at hxd
    calc
      X k - X (k - 1) = ((theta + N : ℕ) : ℤ) - ((theta' + N : ℕ) : ℤ) := hxd
      _ = (theta : ℤ) - (theta' : ℤ) := by omega

end DirectedDistances.PaperProofs.Section5
