module

public import DirectedDistances.KMSW.KMSWWindowFreshVertexStar

/-! presence/missing status transport of the window dart map at vertices allocated
after the window start; boundary rotation, root-frame identification and the
local topology are not treated; not the paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem old_window_edge_endpoint_lt (w : ℕ → Fin 3) (s m e : ℕ)
    (he : e < (kmswStage w s).nextEdge) (b : Bool) :
    (if b then (kmswStage w (s + m)).east e
      else (kmswStage w (s + m)).west e) < (kmswStage w s).nextVertex := by
  have hs := kmswStage_endpoints_stable w (Nat.le_add_right s m) he
  have hb := kmswStage_endpoints_lt_nextVertex w s e he
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem window_boundary_edge_bound (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ++
      (kmswStage w n).LL ++ (kmswStage w n).LR) :
    e < (kmswStage w n).nextEdge :=
  (kmswStage_boundary_ids_lt_nextEdge w n).2 e he

/-- presence/missing status transport of the window dart map at vertices allocated
after the window start; boundary rotation, root-frame identification and the
local topology are not treated; not the paper result. -/
theorem kmswWindowDartMap_present_iff_of_fresh
    (w : ℕ → Fin 3) (s m v : ℕ)
    (_hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (hnew : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v) :
    (kmswStage (fun i => w (s + i)) m).present d.1.val = true ↔
      (kmswStage w (s + m)).present
        (kmswWindowDartMap w s m d).1.val = true := by
  let u := fun i => w (s + i)
  let F := kmswStage u m
  let G₀ := kmswStage w s
  let G := kmswStage w (s + m)
  let data := kmswWindowPatchData w s m
  let e := d.1.val
  let g := data.φ e
  have hrel := kmswWindowPatchData_rel w s m
  change KMSWWindowPatchRel G₀ G F data.φ data.A data.B data.YL
    data.YR data.XL data.XR at hrel
  have he : e < F.nextEdge := d.1.isLt
  have hg : g < G.nextEdge := hrel.edge_bound e he
  have hendpoint := kmswWindowDartMap_vertex w s m d
  change (if d.2 then G.east g else G.west g) =
    kmswWindowPatchVertexMap w s m (stageEndpoint F d) at hendpoint
  rw [hd] at hendpoint
  have hnotOld (hold : g < G₀.nextEdge) : False := by
    have hb := old_window_edge_endpoint_lt w s m g hold d.2
    rw [hendpoint] at hb
    omega
  have hur : (e ∈ F.UR ↔ g ∈ G.UR) := by
    constructor
    · intro heUR
      rw [hrel.ur]
      apply List.mem_append.mpr
      left
      exact List.mem_map.mpr ⟨e, heUR, rfl⟩
    · intro hgUR
      rw [hrel.ur] at hgUR
      rcases List.mem_append.mp hgUR with hgmap | hB
      · rcases List.mem_map.mp hgmap with ⟨f, hfUR, hfg⟩
        have hf : f < F.nextEdge := by
          apply window_boundary_edge_bound u m f
          simp only [List.mem_append]
          tauto
        have hfe : f = e := hrel.edge_injective f hf e he (by
          simpa only [g] using hfg)
        subst f
        exact hfUR
      · have hold : g ∈ G₀.UR := by
          rw [hrel.right_residual]
          simp only [List.mem_append]
          exact Or.inr hB
        have hbound : g < G₀.nextEdge := by
          apply window_boundary_edge_bound w s g
          simp only [List.mem_append]
          tauto
        exact (hnotOld hbound).elim
  have hnotOldLL (hold : g ∈ G₀.LL) : False := by
    have hbound : g < G₀.nextEdge := by
      apply window_boundary_edge_bound w s g
      simp only [List.mem_append]
      tauto
    exact (hnotOld hbound).elim
  have hnotYL (hYL : e ∈ data.YL) : False := by
    have hold : g ∈ G₀.UL.dropLast := by
      rw [hrel.left_residual]
      simp only [List.mem_append]
      right
      exact List.mem_map.mpr ⟨e, hYL, rfl⟩
    have hUL : g ∈ G₀.UL :=
      (List.dropLast_sublist _).subset hold
    have hbound : g < G₀.nextEdge := by
      apply window_boundary_edge_bound w s g
      simp only [List.mem_append]
      tauto
    exact (hnotOld hbound).elim
  have hll : (e ∈ F.LL ↔ g ∈ G.LL) := by
    constructor
    · intro heLL
      rw [hrel.ll_split] at heLL
      rcases List.mem_append.mp heLL with hXL | hYL
      · rw [hrel.ll]
        apply List.mem_append.mpr
        left
        exact List.mem_map.mpr ⟨e, hXL, rfl⟩
      · exact (hnotYL hYL).elim
    · intro hgLL
      rw [hrel.ll] at hgLL
      rcases List.mem_append.mp hgLL with hgXL | hOld
      · rcases List.mem_map.mp hgXL with ⟨f, hfXL, hfg⟩
        have hfLL : f ∈ F.LL := by
          rw [hrel.ll_split]
          exact List.mem_append_left _ hfXL
        have hf : f < F.nextEdge := by
          apply window_boundary_edge_bound u m f
          simp only [List.mem_append]
          tauto
        have hfe : f = e := hrel.edge_injective f hf e he (by
          simpa only [g] using hfg)
        subst f
        rw [hrel.ll_split]
        exact List.mem_append_left _ hfXL
      · exact (hnotOldLL hOld).elim
  have hmiss : F.present e = false ↔ G.present g = false := by
    rw [(kmswStage_status u m).1 e he, (kmswStage_status w (s + m)).1 g hg]
    constructor
    · rintro (hUR | hLL)
      · exact Or.inl (hur.mp hUR)
      · exact Or.inr (hll.mp hLL)
    · rintro (hUR | hLL)
      · exact Or.inl (hur.mpr hUR)
      · exact Or.inr (hll.mpr hLL)
  change F.present e = true ↔ G.present g = true
  constructor
  · intro hp
    exact hrel.present e he hp
  · intro hp
    cases hF : F.present e with
    | true => rfl
    | false =>
      have hfalse := hmiss.mp hF
      rw [hp] at hfalse
      cases hfalse

end DirectedDistances.KMSW
