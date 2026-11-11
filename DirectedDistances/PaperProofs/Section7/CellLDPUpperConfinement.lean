module

public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.RunBoundaryVertexLabels
public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.BusemannUIQBOT
import DirectedDistances.KMSW.KMSWShift
import DirectedDistances.PaperProofs.Section7.LongPathBoundarySegment
import DirectedDistances.PaperProofs.Section7.LongPathFutureBoundaryExit
import DirectedDistances.KMSW.StageFrontier

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem confinement_window_arrow_data (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (e : a ⟶ b) :
    EdgePresent w (kmswWindowEdgeMapInf w n e.val) ∧
      edgeWest w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n a.id ∧
      edgeEast w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n b.id := by
  obtain ⟨m, hm, hp⟩ := e.property.1
  have hr := kmswWindowPatchData_rel w n m
  have hg : kmswWindowEdgeMapInf w n e.val < (kmswStage w (n + m)).nextEdge := by
    rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.edge_bound e.val hm
  refine ⟨⟨n + m, hg, ?_⟩, ?_, ?_⟩
  · rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.present e.val hm hp
  · rw [← (edge_endpoints_eq w hg).1,
      kmswWindowEdgeMapInf_west w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).1, e.property.2.1]
  · rw [← (edge_endpoints_eq w hg).2,
      kmswWindowEdgeMapInf_east w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).2, e.property.2.2]

private theorem confinement_window_path_forward (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (q : Path a b) :
    ∃ p : Path (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n b.id⟩, p.length = q.length := by
  induction q with
  | nil => exact ⟨Path.nil, rfl⟩
  | cons q e ih =>
    obtain ⟨p, hp⟩ := ih
    have he := confinement_window_arrow_data w n e
    refine ⟨p.cons ⟨kmswWindowEdgeMapInf w n e.val, he⟩, ?_⟩
    simp only [Path.length_cons, hp]

private theorem confinement_window_active (w : ℕ → Fin 3) (n t : ℕ) :
    kmswWindowEdgeMapInf w n (act (fun i => w (n + i)) t) = act w (n + t) := by
  rw [kmswWindowEdgeMapInf_eq_stage w n t _ (act_lt_nextEdge _ le_rfl)]
  exact (kmswWindowPatchData_rel w n t).active

private theorem confinement_right_edge_hit (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (j : ℕ) :
    act w (boundaryHitTime w h (j : ℤ)) = kmswRightBoundaryEdge w j := by
  cases j with
  | zero => rw [Nat.cast_zero, boundaryHitTime_zero, kmswRightBoundaryEdge_zero]; rfl
  | succ j => exact boundaryHitTime_right_edge_eq_rightBoundaryEdge w h (by omega)

private theorem confinement_edges_have_preimages (w : ℕ → Fin 3)
    (n σ0 σn : ℕ) (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hfirst : kmswRightBoundaryEdge w σ0 = kmswWindowEdgeMapInf w n
      (kmswRightBoundaryEdge (fun i => w (n + i)) σn))
    {b : PresentVertex w} (p : Path (⟨boundaryVertex w h0 (σ0 : ℤ)⟩ : PresentVertex w) b) :
    ∀ e ∈ pathEdgeList p, ∃ f, EdgePresent (fun i => w (n + i)) f ∧
      kmswWindowEdgeMapInf w n f = e := by
  have htime : boundaryHitTime w h0 (σ0 : ℤ) =
      n + boundaryHitTime (fun i => w (n + i)) hn (σn : ℤ) := by
    apply CutConverse.act_injective w
    rw [confinement_right_edge_hit, ← confinement_window_active,
      confinement_right_edge_hit, hfirst]
  intro e he
  obtain ⟨t, ht, rfl⟩ := directedPath_edges_from_boundaryVertex w h0 (σ0 : ℤ) p e he
  have hnt : n ≤ t := by omega
  refine ⟨act (fun i => w (n + i)) (t - n), ?_, ?_⟩
  · refine ⟨t - n, act_lt_nextEdge _ le_rfl, ?_⟩
    obtain ⟨es, hes⟩ := kmswStage_UL_last (fun i => w (n + i)) (t - n)
    apply (kmswStage_status (fun i => w (n + i)) (t - n)).2.1
    rw [hes]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [confinement_window_active, Nat.add_sub_of_le hnt]

private theorem confinement_path_pullback (w : ℕ → Fin 3) (n : ℕ)
    (a : PresentVertex (fun i => w (n + i))) {b : PresentVertex w}
    (p : Path (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w) b)
    (hp : ∀ e ∈ pathEdgeList p, ∃ f, EdgePresent (fun i => w (n + i)) f ∧
      kmswWindowEdgeMapInf w n f = e) :
    ∃ v, b.id = kmswWindowVertexMapInf w n v ∧
      ∃ q : Path a (⟨v⟩ : PresentVertex (fun i => w (n + i))),
        q.length = p.length ∧
        pathEdgeList p = (pathEdgeList q).map (kmswWindowEdgeMapInf w n) := by
  induction p with
  | nil => exact ⟨a.id, rfl, Path.nil, rfl, rfl⟩
  | @cons b c p e ih =>
    have hp' : ∀ f ∈ pathEdgeList p, ∃ g, EdgePresent (fun i => w (n + i)) g ∧
        kmswWindowEdgeMapInf w n g = f := by
      intro f hf
      exact hp f (List.mem_append_left _ hf)
    obtain ⟨v, hv, q, hq, hqedges⟩ := ih hp'
    obtain ⟨f, hf, hfe⟩ := hp e.val (List.mem_append_right _ (by simp))
    let ef : (⟨edgeWest (fun i => w (n + i)) f⟩ :
        PresentVertex (fun i => w (n + i))) ⟶
        ⟨edgeEast (fun i => w (n + i)) f⟩ := ⟨f, hf, rfl, rfl⟩
    have hdata := confinement_window_arrow_data w n ef
    have hw : edgeWest (fun i => w (n + i)) f = v := by
      apply kmswWindowVertexMapInf_injective w n
      calc
        _ = edgeWest w e.val := by rw [← hfe]; exact hdata.2.1.symm
        _ = b.id := e.property.2.1
        _ = _ := hv
    have hc : c.id = kmswWindowVertexMapInf w n
        (edgeEast (fun i => w (n + i)) f) := by
      rw [← e.property.2.2, ← hfe]
      exact hdata.2.2
    refine ⟨edgeEast (fun i => w (n + i)) f, hc,
      q.cons ⟨f, hf, hw, rfl⟩, ?_, ?_⟩
    · simp only [Path.length_cons, hq]
    · simp only [pathEdgeList, List.map_append, List.map_cons, List.map_nil,
        hqedges, hfe]







theorem path_from_shared_seam_lifts (w : ℕ → Fin 3) (n σ0 σn : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hseam : boundaryVertex w h0 (σ0 : ℤ) = kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)))
    (hmerge : ∀ k : ℕ, 1 ≤ k →
      kmswRightBoundaryEdge w (k - 1 + σ0) = kmswWindowEdgeMapInf w n
        (kmswRightBoundaryEdge (fun i => w (n + i)) (k - 1 + σn)))
    {b : PresentVertex w}
    (p : Path (⟨boundaryVertex w h0 (σ0 : ℤ)⟩ : PresentVertex w) b) :
    ∃ v, b.id = kmswWindowVertexMapInf w n v ∧
      ∃ q : Path (⟨boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)⟩ :
        PresentVertex (fun i => w (n + i))) ⟨v⟩,
      q.length = p.length ∧
      pathEdgeList p = (pathEdgeList q).map (kmswWindowEdgeMapInf w n) := by
  have hfirst := hmerge 1 le_rfl
  simp only [Nat.sub_self, Nat.zero_add] at hfirst
  have hp : ∀ {b : PresentVertex w}
      (r : Path (⟨boundaryVertex w h0 (σ0 : ℤ)⟩ : PresentVertex w) b),
      ∀ e ∈ pathEdgeList r, ∃ f, EdgePresent (fun i => w (n + i)) f ∧
        kmswWindowEdgeMapInf w n f = e :=
    fun r => confinement_edges_have_preimages w n σ0 σn h0 hn hfirst r
  rw [hseam] at hp
  have hlift : ∀ {b : PresentVertex w}
      (r : Path (⟨kmswWindowVertexMapInf w n
        (boundaryVertex (fun i => w (n + i)) hn (σn : ℤ))⟩ : PresentVertex w) b),
      ∃ z, b.id = kmswWindowVertexMapInf w n z ∧
        ∃ q : Path (⟨boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)⟩ :
            PresentVertex (fun i => w (n + i))) ⟨z⟩,
          q.length = r.length ∧
          pathEdgeList r = (pathEdgeList q).map (kmswWindowEdgeMapInf w n) := by
    intro b r
    exact confinement_path_pullback w n _ r (hp r)
  rw [← hseam] at hlift
  exact hlift p






theorem presentLdp_shared_seam_eq (w : ℕ → Fin 3) (n σ0 σn v : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hseam : boundaryVertex w h0 (σ0 : ℤ) = kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)))
    (hmerge : ∀ k : ℕ, 1 ≤ k →
      kmswRightBoundaryEdge w (k - 1 + σ0) = kmswWindowEdgeMapInf w n
        (kmswRightBoundaryEdge (fun i => w (n + i)) (k - 1 + σn))) :
    presentLdp (⟨boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)⟩ :
        PresentVertex (fun i => w (n + i))) ⟨v⟩ =
      presentLdp (⟨boundaryVertex w h0 (σ0 : ℤ)⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n v⟩ := by
  apply le_antisymm
  · have hforward := confinement_window_path_forward w n
      (a := (⟨boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)⟩ :
        PresentVertex (fun i => w (n + i)))) (b := ⟨v⟩)
    rw [← hseam] at hforward
    unfold presentLdp
    apply iSup_le
    intro q
    obtain ⟨p, hp⟩ := hforward q
    exact le_iSup_of_le p (by rw [hp])
  · unfold presentLdp
    apply iSup_le
    intro p
    obtain ⟨z, hz, hq⟩ := path_from_shared_seam_lifts w n σ0 σn h0 hn hseam hmerge p
    have hzv : v = z := kmswWindowVertexMapInf_injective w n hz
    subst z
    obtain ⟨q, hq, _⟩ := hq
    exact le_iSup_of_le q (by rw [hq])

end DirectedDistances.PaperProofs.Section7
