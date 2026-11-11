module

public import DirectedDistances.KMSW.CutVertexDisconnects
public import DirectedDistances.KMSW.LeftmostGeodesicAssembly
import DirectedDistances.KMSW.CutSeparationAE
import DirectedDistances.KMSW.LeftmostGeodesicPlanar

/-! # Infinite present paths visit map cut vertices

present directed path from the source visits every map cut vertex; the renewal times -/

public section
namespace DirectedDistances.KMSW

open Quiver
open DirectedDistances.RandomWalk

private theorem presentVertex_eq_of_id_eq {w : ℕ → Fin 3}
    {x y : PresentVertex w} (h : x.id = y.id) : x = y := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      simp only at h
      subst y
      rfl

private theorem InfinitePresentPath.initial_vertex_ne_of_lt {w : ℕ → Fin 3}
    {v : ℕ} (P : InfinitePresentPath w ⟨v⟩) {i j : ℕ} (hij : i < j) :
    (P.initial i).1 ≠ (P.initial j).1 := by
  intro heq
  let p := (P.initial j).2
  have hpLen : p.length = j := P.prefix_length j
  obtain ⟨z, p₁, p₂, hp, hp₁⟩ :=
    p.exists_eq_comp_of_le_length (n := i) (by omega)
  have hfull : pathEdgeList p₁ ++ pathEdgeList p₂ =
      List.ofFn (fun k : Fin j => P.edge k.val) := by
    rw [← pathEdgeList_comp, ← hp, P.prefix_edges]
  let full : List ℕ := List.ofFn (fun k : Fin j => P.edge k.val)
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
  have hprefix : List.ofFn (fun k : Fin i => P.edge k.val) = full.take i := by
    apply List.ext_get
    · simp [full, Nat.min_eq_left (Nat.le_of_lt hij)]
    · intro k hk₁ hk₂
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

private theorem InfinitePresentPath.edge_injective_of_acyclic {w : ℕ → Fin 3}
    {v : ℕ} (P : InfinitePresentPath w ⟨v⟩) : Function.Injective P.edge := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hi := InfinitePresentPath.edge_outgoing_at_initial w P i
    have hj := InfinitePresentPath.edge_outgoing_at_initial w P j
    have hvertices : (P.initial i).1.id = (P.initial j).1.id := by
      calc
        (P.initial i).1.id = edgeWest w (P.edge i) := hi.2.symm
        _ = edgeWest w (P.edge j) := by rw [hij]
        _ = (P.initial j).1.id := hj.2
    exact P.initial_vertex_ne_of_lt hlt (presentVertex_eq_of_id_eq hvertices)
  · have hj := InfinitePresentPath.edge_outgoing_at_initial w P j
    have hi := InfinitePresentPath.edge_outgoing_at_initial w P i
    have hvertices : (P.initial j).1.id = (P.initial i).1.id := by
      calc
        (P.initial j).1.id = edgeWest w (P.edge j) := hj.2.symm
        _ = edgeWest w (P.edge i) := by rw [hij]
        _ = (P.initial i).1.id := hi.2
    exact P.initial_vertex_ne_of_lt hgt (presentVertex_eq_of_id_eq hvertices)

/-- Every infinite present directed path from the source visits every map cut vertex. -/
theorem InfinitePresentPath.visits_mapCutVertex
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) {v : ℕ}
    (hcut : mapCutVertex w hfin v)
    (P : InfinitePresentPath w ⟨0⟩) :
    ∃ i, edgeWest w (P.edge i) = v ∨ edgeEast w (P.edge i) = v := by
  obtain ⟨n, hnv, _, hA, hB, _⟩ :=
    mapCutVertex_firstVisit_records w hfin htrans hR hL0 hcut
  obtain ⟨i, hi⟩ := kmswInfinitePath_meets_recordVertex w n hA hB P.edge
    (fun i => (InfinitePresentPath.edge_incoming_at_succ w P i).2.trans
      (InfinitePresentPath.edge_outgoing_at_initial w P (i + 1)).2.symm)
    (P.first_edge_outgoing.2) (P.edge_injective_of_acyclic) hfin
  refine ⟨i, ?_⟩
  have hstage := CutConverse.activeInitial_eq w n
  rw [← hstage, ← hnv] at hi
  exact hi

end DirectedDistances.KMSW
