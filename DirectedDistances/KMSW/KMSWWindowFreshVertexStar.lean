module

public import DirectedDistances.KMSW.KMSWWindowPatchStar
public import DirectedDistances.KMSW.KMSWWindowInteriorOuter

/-! geometric dart-star fiber bijection of the window patch at vertices allocated
after the window start, including boundary vertices; presence/missing
equivalence, boundary rotation and root-frame identification are not treated;
not the paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem window_fresh_dart_endpoint (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) :
    stageEndpoint (kmswStage w (s + m)) (kmswWindowDartMap w s m d) =
      kmswWindowPatchVertexMap w s m
        (stageEndpoint (kmswStage (fun i => w (s + i)) m) d) :=
  kmswWindowDartMap_vertex w s m d

private theorem old_dart_endpoint_lt (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage w (s + m)).nextEdge)
    (hd : d.1.val < (kmswStage w s).nextEdge) :
    stageEndpoint (kmswStage w (s + m)) d < (kmswStage w s).nextVertex := by
  have hs := kmswStage_endpoints_stable w (Nat.le_add_right s m) hd
  have hb := kmswStage_endpoints_lt_nextVertex w s d.1.val hd
  cases d with
  | mk e b =>
    cases b
    · simpa [stageEndpoint, hs.1] using hb.1
    · simpa [stageEndpoint, hs.2] using hb.2

private theorem old_dart_cannot_incident (w : ℕ → Fin 3) (s m v : ℕ)
    (hnew : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (g : StageDart (kmswStage w (s + m)).nextEdge)
    (hg : stageEndpoint (kmswStage w (s + m)) g =
      kmswWindowPatchVertexMap w s m v)
    (hold : g.1.val < (kmswStage w s).nextEdge) : False := by
  have hbound := old_dart_endpoint_lt w s m g hold
  have hlarge : (kmswStage w s).nextVertex ≤
      stageEndpoint (kmswStage w (s + m)) g := by
    rw [hg]
    exact hnew
  omega

private theorem fresh_endpoint_eq_of_mapped_eq (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : kmswWindowPatchVertexMap w s m
      (stageEndpoint (kmswStage (fun i => w (s + i)) m) d) =
        kmswWindowPatchVertexMap w s m v) :
    stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v := by
  apply kmswWindowPatchVertexMap_injOn w s m
    (stageEndpoint_lt_nextVertex (fun i => w (s + i)) m d) hv hd

private theorem mapped_edge_fiber (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (g : StageDart (kmswStage w (s + m)).nextEdge)
    (hg : stageEndpoint (kmswStage w (s + m)) g =
      kmswWindowPatchVertexMap w s m v)
    (e : ℕ) (b : Bool)
    (he : e < (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hedge : (kmswWindowPatchData w s m).φ e = g.1.val)
    (hside : b = g.2) :
    ∃ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v ∧
        kmswWindowDartMap w s m d = g := by
  let d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge :=
    (⟨⟨e, he⟩, b⟩)
  have hmap : kmswWindowDartMap w s m d = g := by
    apply Prod.ext
    · apply Fin.ext
      exact hedge
    · exact hside
  have hvertex : kmswWindowPatchVertexMap w s m
      (stageEndpoint (kmswStage (fun i => w (s + i)) m) d) =
        kmswWindowPatchVertexMap w s m v := by
    calc
      _ = stageEndpoint (kmswStage w (s + m))
          (kmswWindowDartMap w s m d) :=
        (window_fresh_dart_endpoint w s m d).symm
      _ = kmswWindowPatchVertexMap w s m v := by rw [hmap, hg]
  have hend := fresh_endpoint_eq_of_mapped_eq w s m v hv d hvertex
  exact ⟨d, hend, hmap⟩

private theorem fresh_triangle_fiber (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (g : StageDart (kmswStage w (s + m)).nextEdge)
    (hg : stageEndpoint (kmswStage w (s + m)) g =
      kmswWindowPatchVertexMap w s m v)
    (j : TriangleCreationTime w) (hj : j.val < s + m)
    (hstart : s ≤ j.val)
    (hgj : (g.1.val, g.2) ∈ stageTriangleDartList w j) :
    ∃ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v ∧
        kmswWindowDartMap w s m d = g := by
  let u := fun i => w (s + i)
  let k := j.val - s
  have hkval : j.val = s + k := by omega
  have hkm : k < m := by omega
  have hbranch : u k = 0 ∨ u k = 1 := by
    simpa only [u, hkval] using j.property
  let jf : TriangleCreationTime u := ⟨k, hbranch⟩
  let jg : TriangleCreationTime w := ⟨s + k, hbranch⟩
  have hjg : j = jg := by
    apply Subtype.ext
    exact hkval
  have hmem : (g.1.val, g.2) ∈ stageTriangleDartList w jg := by
    simpa only [← hjg] using hgj
  have hrot := kmswWindowPatchData_triangle_rotated w s m k hkm hbranch
  have hmapmem := hrot.mem_iff.mpr hmem
  obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hmapmem
  have htime : jf ∈ stageTriangleTimes u m :=
    (mem_stageTriangleTimes u m jf).mpr hkm
  have hedgebound : p.1 < (kmswStage u m).nextEdge := by
    apply stage_face_dart_lt_nextEdge u m p
    exact List.mem_append.mpr
      (Or.inr (List.mem_flatMap.mpr ⟨jf, htime, hp⟩))
  have hedge : (kmswWindowPatchData w s m).φ p.1 = g.1.val :=
    congrArg Prod.fst hpeq
  have hside : p.2 = g.2 := congrArg Prod.snd hpeq
  exact mapped_edge_fiber w s m v hv g hg p.1 p.2 hedgebound hedge hside

/-- geometric dart-star fiber bijection of the window patch at vertices allocated
after the window start, including boundary vertices; presence/missing
equivalence, boundary rotation and root-frame identification are not treated;
not the paper result. -/
theorem kmswWindowDartMap_star_bijective_of_fresh
    (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (hnew : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v) :
    (∀ d₁ d₂ : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d₁ = v →
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d₂ = v →
      kmswWindowDartMap w s m d₁ = kmswWindowDartMap w s m d₂ → d₁ = d₂) ∧
    (∀ g : StageDart (kmswStage w (s + m)).nextEdge,
      stageEndpoint (kmswStage w (s + m)) g = kmswWindowPatchVertexMap w s m v →
      ∃! d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
        stageEndpoint (kmswStage (fun i => w (s + i)) m) d = v ∧
          kmswWindowDartMap w s m d = g) := by
  let u := fun i => w (s + i)
  let F := kmswStage u m
  let G := kmswStage w (s + m)
  let G₀ := kmswStage w s
  let data := kmswWindowPatchData w s m
  have hrel := kmswWindowPatchData_rel w s m
  change KMSWWindowPatchRel G₀ G F data.φ data.A data.B data.YL
    data.YR data.XL data.XR at hrel
  refine ⟨?_, ?_⟩
  · intro d₁ d₂ _ _ heq
    exact kmswWindowDartMap_injective w s m heq
  · intro g hg
    have hfiber : ∃ d : StageDart F.nextEdge,
        stageEndpoint F d = v ∧ kmswWindowDartMap w s m d = g := by
      rcases stage_dart_partition w (s + m) g with hout |
        ⟨j, ⟨hjtime, hgj⟩, hjunique⟩
      · rcases (stageOuterWord_mem_iff w (s + m) g).mp hout with
          ⟨hside, hupper⟩ | ⟨hside, hlower⟩
        · rcases hupper with hUL | hUR
          · rw [hrel.ul] at hUL
            rcases List.mem_append.mp hUL with hA | hmap
            · have hAold : g.1.val < G₀.nextEdge := by
                apply (kmswStage_boundary_ids_lt_nextEdge w s).2
                have hdrop : g.1.val ∈ G₀.UL.dropLast := by
                  rw [hrel.left_residual]
                  exact List.mem_append_left _ hA
                have hm : g.1.val ∈ G₀.UL :=
                  (List.dropLast_sublist _).subset hdrop
                change g.1.val ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
                simp only [List.mem_append]
                exact Or.inl (Or.inl (Or.inl hm))
              exact False.elim (old_dart_cannot_incident w s m v hnew g hg hAold)
            · obtain ⟨e, heF, heq⟩ := List.mem_map.mp hmap
              have he : e < F.nextEdge := by
                apply (kmswStage_boundary_ids_lt_nextEdge u m).2
                change e ∈ F.UL ++ F.UR ++ F.LL ++ F.LR
                simp only [List.mem_append]
                exact Or.inl (Or.inl (Or.inl heF))
              have hedge : data.φ e = g.1.val := heq
              simpa only [u, F, G, data] using
                mapped_edge_fiber w s m v hv g hg e false he hedge hside.symm
          · rw [hrel.ur] at hUR
            rcases List.mem_append.mp hUR with hmap | hB
            · obtain ⟨e, heF, heq⟩ := List.mem_map.mp hmap
              have he : e < F.nextEdge := by
                apply (kmswStage_boundary_ids_lt_nextEdge u m).2
                change e ∈ F.UL ++ F.UR ++ F.LL ++ F.LR
                simp only [List.mem_append]
                exact Or.inl (Or.inl (Or.inr heF))
              have hedge : data.φ e = g.1.val := heq
              simpa only [u, F, G, data] using
                mapped_edge_fiber w s m v hv g hg e false he hedge hside.symm
            · have hBold : g.1.val < G₀.nextEdge := by
                apply (kmswStage_boundary_ids_lt_nextEdge w s).2
                have hm : g.1.val ∈ G₀.UR := by
                  rw [hrel.right_residual]
                  exact List.mem_append_right _ hB
                change g.1.val ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
                simp only [List.mem_append]
                exact Or.inl (Or.inl (Or.inr hm))
              exact False.elim
                (old_dart_cannot_incident w s m v hnew g hg hBold)
        · rcases hlower with hLR | hLL
          · rw [hrel.lr] at hLR
            rcases List.mem_append.mp hLR with hOld | hmap
            · have hOldBound : g.1.val < G₀.nextEdge := by
                apply (kmswStage_boundary_ids_lt_nextEdge w s).2
                change g.1.val ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
                simp only [List.mem_append]
                exact Or.inr hOld
              exact False.elim
                (old_dart_cannot_incident w s m v hnew g hg hOldBound)
            · obtain ⟨e, heXR, heq⟩ := List.mem_map.mp hmap
              have heF : e ∈ F.LR := by
                rw [hrel.lr_split]
                exact List.mem_append_right _ heXR
              have he : e < F.nextEdge := by
                apply (kmswStage_boundary_ids_lt_nextEdge u m).2
                change e ∈ F.UL ++ F.UR ++ F.LL ++ F.LR
                simp only [List.mem_append]
                exact Or.inr heF
              have hedge : data.φ e = g.1.val := heq
              simpa only [u, F, G, data] using
                mapped_edge_fiber w s m v hv g hg e true he hedge hside.symm
          · rw [hrel.ll] at hLL
            rcases List.mem_append.mp hLL with hmap | hOld
            · obtain ⟨e, heXL, heq⟩ := List.mem_map.mp hmap
              have heF : e ∈ F.LL := by
                rw [hrel.ll_split]
                exact List.mem_append_left _ heXL
              have he : e < F.nextEdge := by
                apply (kmswStage_boundary_ids_lt_nextEdge u m).2
                change e ∈ F.UL ++ F.UR ++ F.LL ++ F.LR
                simp only [List.mem_append]
                exact Or.inl (Or.inr heF)
              have hedge : data.φ e = g.1.val := heq
              simpa only [u, F, G, data] using
                mapped_edge_fiber w s m v hv g hg e true he hedge hside.symm
            · have hOldBound : g.1.val < G₀.nextEdge := by
                apply (kmswStage_boundary_ids_lt_nextEdge w s).2
                change g.1.val ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
                simp only [List.mem_append]
                exact Or.inl (Or.inr hOld)
              exact False.elim
                (old_dart_cannot_incident w s m v hnew g hg hOldBound)
      · by_cases hold : j.val < s
        · have hjOld : j ∈ stageTriangleTimes w s :=
            (mem_stageTriangleTimes w s j).mpr hold
          have htri : (g.1.val, g.2) ∈ stageTriangleDartsVal w s :=
            List.mem_flatMap.mpr ⟨j, hjOld, hgj⟩
          have hedge : g.1.val < G₀.nextEdge :=
            stage_face_dart_lt_nextEdge w s (g.1.val, g.2)
              (List.mem_append.mpr (Or.inr htri))
          exact False.elim
            (old_dart_cannot_incident w s m v hnew g hg hedge)
        · have hstart : s ≤ j.val := by omega
          exact fresh_triangle_fiber w s m v hv g hg j hjtime hstart hgj
    rcases hfiber with ⟨d, hd, hmap⟩
    refine ⟨d, ⟨hd, hmap⟩, ?_⟩
    intro e he
    exact (kmswWindowDartMap_injective w s m (hmap.trans he.2.symm)).symm

/-- Concrete boundary regression at the first up-step: the fresh vertex satisfies
the allocation test and has an outer dart, so the interior-star theorem does -/
theorem kmswWindowFreshVertexStar_boundary_example :
    let w : ℕ → Fin 3 := fun _ => 1
    let v := 2
    v < (kmswStage (fun i => w (0 + i)) 1).nextVertex ∧
      (kmswStage w 0).nextVertex ≤ kmswWindowPatchVertexMap w 0 1 v ∧
      ∃ d : StageDart (kmswStage (fun i => w (0 + i)) 1).nextEdge,
        stageEndpoint (kmswStage (fun i => w (0 + i)) 1) d = v ∧
          d ∈ stageOuterWord (fun i => w (0 + i)) 1 ∧
          ¬ KMSWWindowInteriorDart w 0 1 d := by
  dsimp only
  refine ⟨by decide, ?_, ?_⟩
  · decide
  · let d : StageDart (kmswStage (fun i => (1 : Fin 3)) 1).nextEdge :=
      (⟨⟨2, by decide⟩, false⟩)
    refine ⟨d, ?_, ?_, ?_⟩
    · decide
    · decide
    · intro hi
      have hno := (kmswWindowInteriorDart_iff_no_outer
        (fun i => (1 : Fin 3)) 0 1 d).mp hi
      exact hno d rfl (by decide)

end DirectedDistances.KMSW
