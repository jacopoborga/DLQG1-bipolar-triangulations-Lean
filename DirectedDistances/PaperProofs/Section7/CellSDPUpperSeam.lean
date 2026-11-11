module

public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.PaperProofs.Section7.CellLDPUpperConfinement
import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryMerge
import DirectedDistances.PaperProofs.Section7.CellLDPUpperEdgeMerge

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper`, `lem-sdp-tri` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem sdp_window_arrow_data (w : ℕ → Fin 3) (n : ℕ)
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

private theorem sdp_window_path_forward (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (q : Path a b) :
    ∃ p : Path (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n b.id⟩, p.length = q.length := by
  induction q with
  | nil => exact ⟨Path.nil, rfl⟩
  | cons q e ih =>
    obtain ⟨p, hp⟩ := ih
    have he := sdp_window_arrow_data w n e
    refine ⟨p.cons ⟨kmswWindowEdgeMapInf w n e.val, he⟩, ?_⟩
    simp only [Path.length_cons, hp]





theorem presentSdp_shared_seam_eq (w : ℕ → Fin 3) (n σ0 σn v : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hseam : boundaryVertex w h0 (σ0 : ℤ) = kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)))
    (hmerge : ∀ k : ℕ, 1 ≤ k →
      kmswRightBoundaryEdge w (k - 1 + σ0) = kmswWindowEdgeMapInf w n
        (kmswRightBoundaryEdge (fun i => w (n + i)) (k - 1 + σn))) :
    sdp (⟨boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)⟩ :
        PresentVertex (fun i => w (n + i))) ⟨v⟩ =
      sdp (⟨boundaryVertex w h0 (σ0 : ℤ)⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n v⟩ := by
  apply le_antisymm
  · show sdp _ _ ≤ ⨅ p : Path
      (⟨boundaryVertex w h0 (σ0 : ℤ)⟩ : PresentVertex w)
      ⟨kmswWindowVertexMapInf w n v⟩, (p.length : ℕ∞)
    refine le_iInf fun p => ?_
    obtain ⟨z, hz, hq⟩ :=
      path_from_shared_seam_lifts w n σ0 σn h0 hn hseam hmerge p
    have hzv : v = z := kmswWindowVertexMapInf_injective w n hz
    subst z
    obtain ⟨q, hq, _⟩ := hq
    calc
      sdp (⟨boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)⟩ :
          PresentVertex (fun i => w (n + i))) ⟨v⟩ ≤ (q.length : ℕ∞) :=
        sdp_le_length q
      _ = p.length := by rw [hq]
  · show sdp (⟨boundaryVertex w h0 (σ0 : ℤ)⟩ : PresentVertex w)
      ⟨kmswWindowVertexMapInf w n v⟩ ≤ ⨅ q : Path
        (⟨boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)⟩ :
          PresentVertex (fun i => w (n + i))) ⟨v⟩, (q.length : ℕ∞)
    have hforward := sdp_window_path_forward w n
      (a := (⟨boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)⟩ :
        PresentVertex (fun i => w (n + i)))) (b := ⟨v⟩)
    rw [← hseam] at hforward
    refine le_iInf fun q => ?_
    obtain ⟨p, hp⟩ := hforward q
    calc
      sdp (⟨boundaryVertex w h0 (σ0 : ℤ)⟩ : PresentVertex w)
          ⟨kmswWindowVertexMapInf w n v⟩ ≤ (p.length : ℕ∞) := sdp_le_length p
      _ = q.length := by rw [hp]




theorem presentSdp_rightBoundary_seam_eq (w : ℕ → Fin 3) (n v : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) :
    sdp (⟨boundaryVertex (fun i => w (n + i)) hn
        (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)⟩ :
        PresentVertex (fun i => w (n + i))) ⟨v⟩ =
      sdp (⟨boundaryVertex w h0 ((kmswStage w n).LR.length : ℤ)⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n v⟩ := by
  let σ0 := (kmswStage w n).LR.length
  let σn := (kmswStage w n).UR.length + 1
  have hmerge : ∀ k : ℕ, 1 ≤ k →
      kmswRightBoundaryEdge w (k - 1 + σ0) = kmswWindowEdgeMapInf w n
        (kmswRightBoundaryEdge (fun i => w (n + i)) (k - 1 + σn)) := by
    intro k hk
    simpa only [σ0, σn] using
      rightBoundary_edge_merge_explicit w n h0 hn (k - 1)
  have hseam : boundaryVertex w h0 (σ0 : ℤ) = kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hn (σn : ℤ)) := by
    simpa only [zero_add] using
      rightBoundary_vertices_merge_of_edges w n σ0 σn h0 hn hmerge 0
  exact presentSdp_shared_seam_eq w n σ0 σn v h0 hn hseam hmerge




theorem sdp_stage_ge_sdp_limit (w : ℕ → Fin 3) (n : ℕ)
    (a b : StagePresentVertex w n) :
    sdp a b ≥ sdp (⟨a.id⟩ : PresentVertex w) ⟨b.id⟩ :=
  sdp_limit_le_sdp_stage w n a b

end DirectedDistances.PaperProofs.Section7
