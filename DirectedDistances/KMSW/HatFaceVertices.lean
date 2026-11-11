module

public import DirectedDistances.KMSW.HatFaceIso

/-! # Boundary vertices of hatted triangles

Helpers for the hatted half of `lem-quad-kmsw`
three boundary corners, including geometric endpoints of missing edge ids.
Rotation, orientation and planar identification remain; this is not counted
as the paper result. -/

public section
namespace DirectedDistances.KMSW
open Quiver

private def EndpointShape (W E : ℕ → ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  (W t.1 = W t.2.1 ∧ E t.1 = E t.2.2 ∧ E t.2.1 = W t.2.2) ∨
  (E t.1 = E t.2.1 ∧ W t.1 = E t.2.2 ∧ W t.2.1 = W t.2.2)

private theorem predecessor_incidence (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hp : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).east e = (kmswStage w n).west (kmswStage w n).active := by
  let s := kmswStage w n
  obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
  have hrev : xs.reverse = e :: es := by
    simpa [s, hUL, List.reverse_append] using hp
  have hxs : xs = es.reverse ++ [e] := by
    have hh := congrArg List.reverse hrev
    simpa only [List.reverse_reverse, List.reverse_cons, List.reverse_nil] using hh
  have hUL' : s.UL = es.reverse ++ [e, s.active] := by
    rw [hUL, hxs]
    simp [s, List.append_assoc]
  have hc : List.IsChain (fun a b => s.east a = s.west b) s.UL :=
    (kmswStage_boundary_chain_invariant w n).1.left_of_append
  rw [hUL'] at hc
  exact (List.isChain_append_cons_cons.mp hc).2.1

private theorem triangle_endpoint_shape (w : ℕ → Fin 3) (n : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage w n).triangles) :
    EndpointShape (edgeWest w) (edgeEast w) t := by
  induction n with
  | zero => simp [kmswStage, kmswInit] at ht
  | succ n ih =>
    by_cases hold : t ∈ (kmswStage w n).triangles
    · exact ih hold
    have hb := triBound_stage w (n + 1) t ht
    have h1 := edge_endpoints_eq w hb.1
    have h2 := edge_endpoints_eq w hb.2.1
    have h3 := edge_endpoints_eq w hb.2.2
    unfold EndpointShape
    rw [← h1.1, ← h1.2, ← h2.1, ← h2.2, ← h3.1, ← h3.2]
    change t ∈ (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).triangles at ht
    change EndpointShape (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).west
      (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).east t
    have ha : (kmswStage w n).active < (kmswStage w n).nextEdge := (kmswStage_boundary_ids_lt_nextEdge w n).1
    have ha0 : (kmswStage w n).active ≠ (kmswStage w n).nextEdge := by omega
    have ha1 : (kmswStage w n).active ≠ (kmswStage w n).nextEdge + 1 := by omega
    cases hc : kmswCodeStep (w n) with
    | down =>
      cases hu : (kmswStage w n).UR <;> simp [hc, kmswStepOfStep, hu, State.addEdge] at ht
      all_goals exact (hold ht).elim
    | up =>
      simp only [hc, kmswStepOfStep, State.addEdge, List.mem_append,
        List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact (hold ht).elim
      · apply Or.inl
        simp [kmswStepOfStep, State.addEdge, ha0, ha1]
    | left =>
      cases hp : (kmswStage w n).UL.dropLast.reverse with
      | nil =>
        simp only [hc, kmswStepOfStep, hp, State.addEdge, List.mem_append,
          List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact (hold ht).elim
        · apply Or.inr
          simp [kmswStepOfStep, hp, State.addEdge, ha0, ha1]
      | cons e es =>
        have he : e < (kmswStage w n).nextEdge := by
          apply (kmswStage_boundary_ids_lt_nextEdge w n).2
          have hm : e ∈ (kmswStage w n).UL := List.mem_of_mem_dropLast
            (List.mem_reverse.mp (by rw [hp]; simp))
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inl hm))
        have he0 : e ≠ (kmswStage w n).nextEdge := by omega
        have hi := predecessor_incidence w n e es hp
        simp only [hc, kmswStepOfStep, hp, State.addEdge, List.mem_append,
          List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact (hold ht).elim
        · apply Or.inr
          simpa [hc, kmswStepOfStep, hp, State.addEdge, ha0, he0] using hi.symm


/-- Three canonical corners of a stored triangle: the endpoints of its old
active edge and the remaining corner on its new active edge. The endpoint
characterization below applies to stored triangles (`lem-quad-kmsw`, -/
@[expose] def triangleCorners (w : ℕ → Fin 3) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (edgeWest w t.1, edgeEast w t.1,
    if edgeWest w t.1 = edgeWest w t.2.1 then edgeEast w t.2.1
    else edgeWest w t.2.1)

/-- The three corners are exactly all boundary endpoints, including endpoints -/
theorem triangleCorners_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage w n).triangles) (v : ℕ) :
    v ∈ [(triangleCorners w t).1, (triangleCorners w t).2.1,
      (triangleCorners w t).2.2] ↔
    ∃ e ∈ [t.1, t.2.1, t.2.2], v = edgeWest w e ∨ v = edgeEast w e := by
  have hs := triangle_endpoint_shape w n t ht
  rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  all_goals
    simp only [triangleCorners]
    split_ifs
    all_goals simp_all only [List.mem_cons, List.not_mem_nil, or_false]
    all_goals aesop

/-- The canonical corners of a stored triangle are pairwise distinct -/
theorem triangleCorners_distinct (w : ℕ → Fin 3) (n : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage w n).triangles) :
    (triangleCorners w t).1 ≠ (triangleCorners w t).2.1 ∧
      (triangleCorners w t).1 ≠ (triangleCorners w t).2.2 ∧
      (triangleCorners w t).2.1 ≠ (triangleCorners w t).2.2 := by
  have hb := triBound_stage w n t ht
  have strict : ∀ e, e < (kmswStage w n).nextEdge →
      kmswStageRank w n (edgeWest w e) < kmswStageRank w n (edgeEast w e) := by
    intro e he
    simpa only [(edge_endpoints_eq w he).1, (edge_endpoints_eq w he).2] using
      kmswStageRank_strict w n e he
  have r1 := strict t.1 hb.1
  have r2 := strict t.2.1 hb.2.1
  have r3 := strict t.2.2 hb.2.2
  rcases triangle_endpoint_shape w n t ht with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [← h1] at r2
    rw [← h3, ← h2] at r3
    simp only [triangleCorners, ite_eq_left h1]
    refine ⟨?_, ?_, ?_⟩
    all_goals
      intro hv
      have hv' := congrArg (kmswStageRank w n) hv
      linarith only [r1, r2, r3, hv']
  · rw [← h1] at r2
    rw [← h3, ← h2] at r3
    have hh : edgeWest w t.1 ≠ edgeWest w t.2.1 := by
      intro hv
      have hv' := congrArg (kmswStageRank w n) hv
      linarith only [r3, hv']
    simp only [triangleCorners, ite_eq_right hh]
    refine ⟨?_, hh, ?_⟩
    all_goals
      intro hv
      have hv' := congrArg (kmswStageRank w n) hv
      linarith only [r1, r2, r3, hv']

/-- Triangle-vertex lemma at the limit: there are three corners containing
all six boundary endpoints, and every corner occurs as an endpoint -/
theorem triangle_vertices (w : ℕ → Fin 3) (n : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage w n).triangles) :
    ∃ x y z : ℕ, (x ≠ y ∧ x ≠ z ∧ y ≠ z) ∧
      (∀ e ∈ [t.1, t.2.1, t.2.2],
        edgeWest w e ∈ [x, y, z] ∧ edgeEast w e ∈ [x, y, z]) ∧
      (∀ v ∈ [x, y, z],
        ∃ e ∈ [t.1, t.2.1, t.2.2], v = edgeWest w e ∨ v = edgeEast w e) := by
  refine ⟨(triangleCorners w t).1, (triangleCorners w t).2.1,
    (triangleCorners w t).2.2, triangleCorners_distinct w n t ht, ?_, ?_⟩
  · intro e he
    exact ⟨(triangleCorners_endpoints w n t ht _).mpr ⟨e, he, Or.inl rfl⟩,
      (triangleCorners_endpoints w n t ht _).mpr ⟨e, he, Or.inr rfl⟩⟩
  · intro v hv
    exact (triangleCorners_endpoints w n t ht v).mp hv

/-- The same three limit corners describe the endpoints at every later
stage; creation-time endpoints never move (`lem-quad-kmsw`, -/
theorem triangleCorners_stage_endpoints (w : ℕ → Fin 3) (n m : ℕ)
    (hnm : n ≤ m) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage w n).triangles) (v : ℕ) :
    v ∈ [(triangleCorners w t).1, (triangleCorners w t).2.1,
      (triangleCorners w t).2.2] ↔
    ∃ e ∈ [t.1, t.2.1, t.2.2],
      v = (kmswStage w m).west e ∨ v = (kmswStage w m).east e := by
  have hb := triBound_stage w m t (triangles_sub_stage w hnm t ht)
  have ends : ∀ e ∈ [t.1, t.2.1, t.2.2],
      (kmswStage w m).west e = edgeWest w e ∧
      (kmswStage w m).east e = edgeEast w e := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact edge_endpoints_eq w hb.1
    · exact edge_endpoints_eq w hb.2.1
    · exact edge_endpoints_eq w hb.2.2
  rw [triangleCorners_endpoints w n t ht v]
  constructor <;> rintro ⟨e, he, hv⟩ <;> refine ⟨e, he, ?_⟩
  · simpa only [(ends e he).1, (ends e he).2] using hv
  · simpa only [(ends e he).1, (ends e he).2] using hv

/-- Reachability of the three canonical boundary corners, the face condition
in the hatted half of `lem-quad-kmsw` -/
@[expose] def HatCornersReachable (w : ℕ → Fin 3) (t : ℕ × ℕ × ℕ) : Prop :=
  Reachable (⟨0⟩ : PresentVertex w) ⟨(triangleCorners w t).1⟩ ∧
  Reachable (⟨0⟩ : PresentVertex w) ⟨(triangleCorners w t).2.1⟩ ∧
  Reachable (⟨0⟩ : PresentVertex w) ⟨(triangleCorners w t).2.2⟩

/-- All endpoints are reachable exactly when the three boundary corners are -/
theorem hatTriangleReachable_iff_corners (w : ℕ → Fin 3) (n : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage w n).triangles) :
    HatTriangleReachable w t ↔ HatCornersReachable w t := by
  have hc : ∀ v ∈ [(triangleCorners w t).1, (triangleCorners w t).2.1,
      (triangleCorners w t).2.2], HatTriangleReachable w t →
      Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩ := by
    intro v hv hr
    obtain ⟨e, he, hv⟩ := (triangleCorners_endpoints w n t ht v).mp hv
    rcases hv with rfl | rfl
    · exact (hr e he).1
    · exact (hr e he).2
  constructor
  · intro hr
    exact ⟨hc _ (by simp) hr, hc _ (by simp) hr, hc _ (by simp) hr⟩
  · intro hr e he
    have hv : ∀ v ∈ [(triangleCorners w t).1, (triangleCorners w t).2.1,
        (triangleCorners w t).2.2], Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩ := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hr.1
      · exact hr.2.1
      · exact hr.2.2
    exact ⟨hv _ ((triangleCorners_endpoints w n t ht _).mpr ⟨e, he, Or.inl rfl⟩),
      hv _ ((triangleCorners_endpoints w n t ht _).mpr ⟨e, he, Or.inr rfl⟩)⟩

/-- Global stored triangles whose three boundary vertices are reachable:
the source face condition for the hatted half of `lem-quad-kmsw` -/
@[expose] def GlobalHatTriSrc (w : ℕ → Fin 3) :=
  {t : ℕ × ℕ × ℕ // ∃ n, t ∈ (kmswStage w n).triangles ∧ HatCornersReachable w t}

/-- Translate the endpoint-based global face carrier to the source's -/
@[expose] def globalHatTriSrcEquiv (w : ℕ → Fin 3) : GlobalHatTri w ≃ GlobalHatTriSrc w where
  toFun t := ⟨t.1, by
    obtain ⟨n, ht, hr⟩ := t.2
    exact ⟨n, ht, (hatTriangleReachable_iff_corners w n t.1 ht).mp hr⟩⟩
  invFun t := ⟨t.1, by
    obtain ⟨n, ht, hr⟩ := t.2
    exact ⟨n, ht, (hatTriangleReachable_iff_corners w n t.1 ht).mpr hr⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The explicit hatted face equivalence with the source's three-vertex
Rotation, orientation and planar identification remain; helper only, not counted. -/
@[expose] noncomputable def hatSourceFaceEquiv (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    HatLocalTri w h ≃ GlobalHatTriSrc w :=
  (hatLimitFaceEquiv w h).trans (globalHatTriSrcEquiv w)

/-- The source face equivalence uses exactly the explicit graph edge map -/
theorem hatSourceFaceEquiv_compatible (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (t : HatLocalTri w h) :
    (hatSourceFaceEquiv w h t).1 =
      ((hatExplicitEdgeEquiv w h ⟨t.1.1, (hatLocalTri_edges_present w h t).1⟩).1,
       (hatExplicitEdgeEquiv w h ⟨t.1.2.1, (hatLocalTri_edges_present w h t).2.1⟩).1,
       (hatExplicitEdgeEquiv w h ⟨t.1.2.2, (hatLocalTri_edges_present w h t).2.2⟩).1) :=
  hatLimitFaceEquiv_compatible w h t

/-- Every allocated local id has a globally present counterpart with reachable
endpoints; no triangle-incidence premise is required. This includes any
currently missing outer-boundary id. Present means eventual `EdgePresent`, not a flag -/
theorem hatLimit_allocated_edge_present_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m e : ℕ)
    (he : e < (kmswStage (hatCodes w h) m).nextEdge) :
    EdgePresent (hatCodes w h) e ∧ EdgePresent w (hatLimitEdgeMap w h e) ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w (hatLimitEdgeMap w h e)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w (hatLimitEdgeMap w h e)⟩ := by
  have hp := hatLocal_allocated_edge_present w h m e he
  have hd := (hatExplicitEdgeEquiv w h ⟨e, hp⟩).2
  rw [hatExplicitEdgeEquiv_apply] at hd
  exact ⟨hp, hd⟩

/-- At aligned finite stages, both present and missing flags are preserved
for every allocated local id. Such a missing flag is temporary: the preceding
limit theorem gives eventual presence of both ids (`lem-quad-kmsw`, -/
theorem hatLimit_stage_present_eq (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m e : ℕ) (he : e < (kmswStage (hatCodes w h) m).nextEdge) :
    (kmswStage (hatCodes w h) m).present e =
      (kmswStage w (quadrantRStageTime w h m)).present (hatLimitEdgeMap w h e) := by
  have D := hatLimitExplicitInput w h
  have hi := D.stage_sim m
  have hb := hi.edge_bound e he
  have hr := (hatLimit_allocated_edge_present_reachable w h m e he).2.2
  have hend := edge_endpoints_eq w hb
  have iff_true : (kmswStage (hatCodes w h) m).present e = true ↔
      (kmswStage w (quadrantRStageTime w h m)).present (hatLimitEdgeMap w h e) = true := by
    constructor
    · exact hi.present e he
    · intro hp
      have hm : hatLimitEdgeMap w h e ∈
          stageReachablePresentEdges w (quadrantRStageTime w h m) := by
        refine ⟨hb, hp, ?_, ?_⟩
        · simpa only [hend.1] using hr.1
        · simpa only [hend.2] using hr.2
      rw [← D.edge_image m] at hm
      obtain ⟨f, ⟨hf, hpf⟩, hfe⟩ := hm
      have hEq : f = e := hi.edge_injective f e hf he hfe
      exact hEq ▸ hpf
  cases hl : (kmswStage (hatCodes w h) m).present e <;>
    cases hg : (kmswStage w (quadrantRStageTime w h m)).present (hatLimitEdgeMap w h e) <;>
    simp_all only [Bool.false_eq_true, false_iff, iff_false, not_true_eq_false]

/-- Missing-id transfer for every edge of a local triangle: both local and
image ids are eventually present, and the image endpoints are reachable -/
theorem hatLocalTri_image_edges_present (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (t : HatLocalTri w h) :
    ∀ e ∈ [t.1.1, t.1.2.1, t.1.2.2],
      EdgePresent (hatCodes w h) e ∧ EdgePresent w (hatLimitEdgeMap w h e) ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w (hatLimitEdgeMap w h e)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w (hatLimitEdgeMap w h e)⟩ := by
  obtain ⟨m, hm⟩ := t.2
  have hb := triBound_stage (hatCodes w h) m t.1 hm
  intro e he
  apply hatLimit_allocated_edge_present_reachable w h m e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2

/-- A finite-stage missing flag is not permanent absence: the word up, down
creates a triangle with missing id `2` and then activates that id. Thus
replacing eventual presence by current presence is false (`lem-quad-kmsw`, -/
theorem triangle_missing_flag_counterexample :
    let u : ℕ → Fin 3 := fun n => if n = 0 then 1 else 2
    (0, 1, 2) ∈ (kmswStage u 1).triangles ∧
      (kmswStage u 1).present 2 = false ∧
      (kmswStage u 2).present 2 = true := by
  decide

end DirectedDistances.KMSW
