module

public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.RunBoundaryVertexLabels
public import DirectedDistances.KMSW.BusemannUIQBOT
import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryRoutes
import DirectedDistances.PaperProofs.Section7.CellLDPUpperRouteUp

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem concat_window_arrow_data (w : ℕ → Fin 3) (n : ℕ)
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




theorem cell_window_path_forward (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (q : Path a b) :
    ∃ p : Path (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n b.id⟩, p.length = q.length := by
  induction q with
  | nil => exact ⟨Path.nil, rfl⟩
  | cons q e ih =>
    obtain ⟨p, hp⟩ := ih
    have he := concat_window_arrow_data w n e
    refine ⟨p.cons ⟨kmswWindowEdgeMapInf w n e.val, he⟩, ?_⟩
    simp only [Path.length_cons, hp]




theorem cell_path_concat_presentLdp_le (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (x y : StagePresentVertex w n) (hx : x.id < (kmswStage w n).nextVertex)
    (hy : y.id < (kmswStage w n).nextVertex) (p : Path x y) :
    ∃ ℓ k : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ ℓ ∧
      ℓ ≤ ((kmswStage w n).LR.length : ℤ) ∧
      -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
      k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
      ∀ v : PresentVertex (fun i => w (n + i)),
        ((p.length : ℕ∞) : WithBot ℕ∞) +
            presentLdp (⟨boundaryVertex (fun i => w (n + i)) hn k⟩ :
              PresentVertex (fun i => w (n + i))) v ≤
          presentLdp (⟨boundaryVertex w h0 ℓ⟩ : PresentVertex w)
            ⟨kmswWindowVertexMapInf w n v.id⟩ := by
  obtain ⟨ℓ, hℓL, hℓR, _, _, ⟨a⟩⟩ := stage_cell_lower_boundary_route w h0 n x hx
  obtain ⟨k, hkL, hkR, ⟨b⟩⟩ := stage_cell_upper_boundary_route w n hn y hy
  refine ⟨ℓ, k, hℓL, hℓR, hkL, hkR, fun v => ?_⟩
  let z : PresentVertex (fun i => w (n + i)) := ⟨boundaryVertex _ hn k⟩
  have hpath (q : Path z v) :
      ((p.length : ℕ∞) : WithBot ℕ∞) + ((q.length : ℕ∞) : WithBot ℕ∞) ≤
        presentLdp (⟨boundaryVertex w h0 ℓ⟩ : PresentVertex w)
          ⟨kmswWindowVertexMapInf w n v.id⟩ := by
    obtain ⟨q', hq'⟩ := cell_window_path_forward w n q
    let c : Path (⟨boundaryVertex w h0 ℓ⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n z.id⟩ :=
      (stageToLimit w n).mapPath ((a.comp p).comp b)
    have hc : c.length = ((a.comp p).comp b).length :=
      stageToLimit_length w n ((a.comp p).comp b)
    let r := c.comp q'
    have hlen : p.length + q.length ≤ r.length := by
      dsimp only [r]
      rw [Path.length_comp, hc, Path.length_comp, Path.length_comp, hq']
      omega
    apply le_trans _ (le_iSup (fun r => ((r.length : ℕ∞) : WithBot ℕ∞)) r)
    rw [← WithBot.coe_add, WithBot.coe_le_coe, ← ENat.natCast_add]
    exact ENat.natCast_le_natCast.mpr hlen
  change ((p.length : ℕ∞) : WithBot ℕ∞) + presentLdp z v ≤ _
  cases isEmpty_or_nonempty (Path z v) with
  | inl he =>
    let := he
    simp only [presentLdp, iSup_of_empty, WithBot.add_bot, bot_le]
  | inr he =>
    let := he
    have hsup : presentLdp z v =
        (↑(⨆ q : Path z v, (q.length : ℕ∞)) : WithBot ℕ∞) :=
      (WithBot.coe_iSup (f := fun q : Path z v => (q.length : ℕ∞))
        (OrderTop.bddAbove _)).symm
    rw [hsup, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (OrderTop.bddAbove _)]
    apply iSup_le
    intro q
    simpa only [WithBot.coe_add] using hpath q

end DirectedDistances.PaperProofs.Section7
