module

public import DirectedDistances.KMSW.HatTriangleExact
public import DirectedDistances.KMSW.HatLimitIncidenceIso
public import DirectedDistances.KMSW.HatInputAssembly
import DirectedDistances.KMSW.SDPIdentifyBdy

/-! # Explicit graph maps and the limit triangle bijection for the hatted code

Graph and unoriented face helpers for the hatted half of `lem-quad-kmsw`
the same first-allocation limit of `hatAllEdgeMap`. Rotation, orientation of
faces and the planar identification remain; this helper is not counted as
the paper result. -/

public section
namespace DirectedDistances.KMSW
open Quiver

/-- First-allocation edge map for the hatted half of `lem-quad-kmsw` -/
@[expose] noncomputable def hatLimitEdgeMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ :=
  limitEdgeMap (hatAllEdgeMap w h) (hatCodes w h)

/-- First-allocation vertex map for the hatted half of `lem-quad-kmsw` -/
@[expose] noncomputable def hatLimitVertexMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ℕ → ℕ :=
  limitVertexMap (hatAllVertexMap w h) (hatCodes w h)

/-- The explicit edge limit agrees with every stage allocating that edge -/
theorem hatLimitEdgeMap_eq_stage (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m e : ℕ) (he : e < (kmswStage (hatCodes w h) m).nextEdge) :
    hatLimitEdgeMap w h e = hatAllEdgeMap w h m e :=
  limitEdgeMap_eq_of_allocated _ (hatAllEdgeMap_extend w h) m e he

/-- The explicit vertex limit agrees with every stage allocating that vertex -/
theorem hatLimitVertexMap_eq_stage (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m a : ℕ) (ha : a < (kmswStage (hatCodes w h) m).nextVertex) :
    hatLimitVertexMap w h a = hatAllVertexMap w h m a :=
  limitVertexMap_eq_of_allocated _ (hatAllVertexMap_extend w h) m a ha

/-- The explicit maps satisfy every field of the graph limit input, with no -/
theorem hatLimitExplicitInput (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    HatImageLimitInput (hatCodes w h) w (quadrantRStageTime w h)
      (hatLimitEdgeMap w h) (hatLimitVertexMap w h) := by
  exact hatImageLimitInput_of_coherent_stage_maps
    (quadrantRStageTime w h) (hatAllEdgeMap w h) (hatAllVertexMap w h)
    (fun _ _ hmn => quadrantRStageTime_mono w h hmn)
    (quadrantRStageTime_unbounded w h)
    (hatAllEdgeMap_extend w h) (hatAllVertexMap_extend w h)
    (fun m => (hatAll_sim w h m).incidenceSim)
    (hatAllEdgeMap_set_image_eq_reachable w h)
    (hatAllVertexMap_root w h) (hatCodes_allocated_nonroot_incident w h)

/-- The graph edge equivalence with the explicit first-allocation map -/
@[expose] noncomputable def hatExplicitEdgeEquiv (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    {e : ℕ // EdgePresent (hatCodes w h) e} ≃
      {e : ℕ // EdgePresent w e ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩} :=
  hatLimitEdgeEquiv (hatLimitExplicitInput w h)

/-- The graph vertex equivalence with the explicit first-allocation map -/
@[expose] noncomputable def hatExplicitVertexEquiv (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    {a : PresentVertex (hatCodes w h) //
      ∃ m, a.id < (kmswStage (hatCodes w h) m).nextVertex} ≃
      {v : PresentVertex w // Reachable (⟨0⟩ : PresentVertex w) v} :=
  hatLimitVertexEquiv (hatLimitExplicitInput w h)

/-- Local limit triangles, represented by their stored edge triples -/
@[expose] def HatLocalTri (w : ℕ → Fin 3) (h : HasFlowLineHits w) :=
  {t : ℕ × ℕ × ℕ // ∃ m, t ∈ (kmswStage (hatCodes w h) m).triangles}

/-- Global limit triangles with all boundary endpoints root reachable -/
@[expose] def GlobalHatTri (w : ℕ → Fin 3) :=
  {t : ℕ × ℕ × ℕ // ∃ n, t ∈ (kmswStage w n).triangles ∧ HatTriangleReachable w t}

private theorem hatLimitEdgeMap_inj_alloc (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {e f : ℕ}
    (he : ∃ m, e < (kmswStage (hatCodes w h) m).nextEdge)
    (hf : ∃ m, f < (kmswStage (hatCodes w h) m).nextEdge)
    (hef : hatLimitEdgeMap w h e = hatLimitEdgeMap w h f) : e = f := by
  obtain ⟨m, hm⟩ := he
  obtain ⟨n, hn⟩ := hf
  exact ((hatLimitExplicitInput w h).stage_sim (max m n)).edge_injective e f
    (hm.trans_le (kmswStage_nextEdge_mono _ (Nat.le_max_left m n)))
    (hn.trans_le (kmswStage_nextEdge_mono _ (Nat.le_max_right m n))) hef

private theorem hatLimitEdgeMap_endpoints_reachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m e : ℕ)
    (he : e < (kmswStage (hatCodes w h) m).nextEdge) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w (hatLimitEdgeMap w h e)⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w (hatLimitEdgeMap w h e)⟩ := by
  have D := hatLimitExplicitInput w h
  have hb := (D.stage_sim m).edge_bound e he
  have hi := (D.stage_sim m).incidence e he
  have ha := kmswStage_endpoints_lt_nextVertex (hatCodes w h) m e he
  have hw := edge_endpoints_eq w hb
  rw [← hw.1, ← hw.2, hi.1, hi.2]
  exact ⟨alloc_reachable D ⟨m, ha.1⟩, alloc_reachable D ⟨m, ha.2⟩⟩

private theorem hatFace_R_unbounded (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ a : ℤ, ∃ n, R w n ≤ a := by
  have hlevels : ∀ k : ℕ, ∃ n, R w n = -(k : ℤ) := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp [R]⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, _, hm⟩ := h.2 n
      exact ⟨m, by rw [hm, hn]; omega⟩
  intro a
  cases a with
  | ofNat a => exact ⟨0, by simp [R]⟩
  | negSucc k =>
    obtain ⟨n, hn⟩ := hlevels (k + 1)
    exact ⟨n, by omega⟩

private theorem hatFace_LL_nil (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) : (kmswStage (hatCodes w h) m).LL = [] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (kmswStepOfStep (kmswStage (hatCodes w h) m)
      (kmswCodeStep (hatCodes w h m))).LL = []
    cases hc : kmswCodeStep (hatCodes w h m) with
    | left =>
      have hn := noFreshLeftSource_hatCodes w h m hc
      cases hp : (kmswStage (hatCodes w h) m).UL.dropLast.reverse with
      | nil => exact (hn hp).elim
      | cons e es => simpa only [kmswStepOfStep, hp, State.addEdge] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | down =>
      cases hu : (kmswStage (hatCodes w h) m).UR <;>
        simpa only [kmswStepOfStep, hu, State.addEdge] using ih

/-- Every allocated local edge is eventually present. In particular all
components of a local triangle lie in the graph edge equivalence's domain -/
theorem hatLocal_allocated_edge_present (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m e : ℕ) (he : e < (kmswStage (hatCodes w h) m).nextEdge) :
    EdgePresent (hatCodes w h) e := by
  by_cases hp : (kmswStage (hatCodes w h) m).present e = true
  · exact ⟨m, he, hp⟩
  · have hf : (kmswStage (hatCodes w h) m).present e = false := by
      simpa only [Bool.not_eq_true] using hp
    have hu : e ∈ (kmswStage (hatCodes w h) m).UR := by
      have hs := ((kmswStage_status (hatCodes w h) m).1 e he).mp hf
      simpa only [hatFace_LL_nil w h m, List.not_mem_nil, or_false] using hs
    have D := hatLimitExplicitInput w h
    have hgu : hatLimitEdgeMap w h e ∈
        (kmswStage w (quadrantRStageTime w h m)).UR :=
      (D.stage_sim m).ur_prefix.subset (List.mem_map.mpr ⟨e, hu, rfl⟩)
    obtain ⟨n, hmn, hpn⟩ := kmswStage_UR_edge_eventually_present_of_R_unbounded
      w (hatFace_R_unbounded w h) (quadrantRStageTime w h m) _ hgu
    have hbn := ((D.stage_sim m).edge_bound e he).trans_le
      (kmswStage_nextEdge_mono w hmn)
    have hr := hatLimitEdgeMap_endpoints_reachable w h m e he
    obtain ⟨f, hf, hfe⟩ := edge_cover D ⟨n, hbn, hpn⟩ hr.1 hr.2
    have halloc : ∃ j, f < (kmswStage (hatCodes w h) j).nextEdge := by
      obtain ⟨j, hj, _⟩ := hf
      exact ⟨j, hj⟩
    have hEq : f = e := hatLimitEdgeMap_inj_alloc w h halloc ⟨m, he⟩ hfe
    exact hEq ▸ hf

/-- The componentwise explicit limit map sends local triangles to reachable
Only the unoriented edge-triple layer is asserted. -/
theorem hatLimitTriangle_mem (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ (kmswStage (hatCodes w h) m).triangles) :
    let s := (hatLimitEdgeMap w h t.1,
      hatLimitEdgeMap w h t.2.1, hatLimitEdgeMap w h t.2.2)
    s ∈ (kmswStage w (quadrantRStageTime w h m)).triangles ∧
      HatTriangleReachable w s := by
  obtain ⟨b1, b2, b3⟩ := triBound_stage (hatCodes w h) m t ht
  constructor
  · rw [hatLimitEdgeMap_eq_stage w h m _ b1,
      hatLimitEdgeMap_eq_stage w h m _ b2, hatLimitEdgeMap_eq_stage w h m _ b3]
    exact hatAll_triSim_of_le w h (le_refl m) t ht
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact hatLimitEdgeMap_endpoints_reachable w h m _ b1
    · exact hatLimitEdgeMap_endpoints_reachable w h m _ b2
    · exact hatLimitEdgeMap_endpoints_reachable w h m _ b3

/-- Every reachable global limit triangle has a local preimage under the -/
theorem hatLimitTriangle_surj (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (s : GlobalHatTri w) :
    ∃ t : HatLocalTri w h,
      (hatLimitEdgeMap w h t.1.1, hatLimitEdgeMap w h t.1.2.1,
        hatLimitEdgeMap w h t.1.2.2) = s.1 := by
  obtain ⟨n, hn, hr⟩ := s.2
  obtain ⟨m, hm⟩ := quadrantRStageTime_unbounded w h n
  obtain ⟨t, ht, hts⟩ := hatAll_triangle_exact w h m s.1
    (triangles_sub_stage w hm s.1 hn) hr
  obtain ⟨b1, b2, b3⟩ := triBound_stage (hatCodes w h) m t ht
  refine ⟨⟨t, m, ht⟩, ?_⟩
  change (hatLimitEdgeMap w h t.1, hatLimitEdgeMap w h t.2.1,
    hatLimitEdgeMap w h t.2.2) = s.1
  rwa [hatLimitEdgeMap_eq_stage w h m _ b1,
    hatLimitEdgeMap_eq_stage w h m _ b2, hatLimitEdgeMap_eq_stage w h m _ b3]

/-- Limit bijection of stored edge triples for the hatted half of
use precisely the explicit graph edge map. Rotation, oriented face cycles
and planar identification remain; not counted as the paper result. -/
@[expose] noncomputable def hatLimitFaceEquiv (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : HatLocalTri w h ≃ GlobalHatTri w :=
  Equiv.ofBijective
    (fun t => ⟨(hatLimitEdgeMap w h t.1.1, hatLimitEdgeMap w h t.1.2.1,
      hatLimitEdgeMap w h t.1.2.2), by
        obtain ⟨m, hm⟩ := t.2
        exact ⟨quadrantRStageTime w h m, hatLimitTriangle_mem w h m t.1 hm⟩⟩)
    (by
      constructor
      · intro t s hts
        obtain ⟨m, hm⟩ := t.2
        obtain ⟨n, hn⟩ := s.2
        obtain ⟨b1, b2, b3⟩ := triBound_stage (hatCodes w h) m t.1 hm
        obtain ⟨c1, c2, c3⟩ := triBound_stage (hatCodes w h) n s.1 hn
        have he := congrArg Subtype.val hts
        apply Subtype.ext
        apply Prod.ext
        · exact hatLimitEdgeMap_inj_alloc w h ⟨m, b1⟩ ⟨n, c1⟩
            (congrArg Prod.fst he)
        · apply Prod.ext
          · exact hatLimitEdgeMap_inj_alloc w h ⟨m, b2⟩ ⟨n, c2⟩
              (congrArg (fun x => x.2.1) he)
          · exact hatLimitEdgeMap_inj_alloc w h ⟨m, b3⟩ ⟨n, c3⟩
              (congrArg (fun x => x.2.2) he)
      · intro s
        obtain ⟨t, ht⟩ := hatLimitTriangle_surj w h s
        exact ⟨t, Subtype.ext ht⟩)

/-- The explicit vertex equivalence evaluates by `hatLimitVertexMap` -/
theorem hatExplicitVertexEquiv_apply (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a : {a : PresentVertex (hatCodes w h) //
      ∃ m, a.id < (kmswStage (hatCodes w h) m).nextVertex}) :
    (hatExplicitVertexEquiv w h a).1.id = hatLimitVertexMap w h a.1.id := rfl

/-- The explicit edge equivalence evaluates by `hatLimitEdgeMap` -/
theorem hatExplicitEdgeEquiv_apply (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (e : {e : ℕ // EdgePresent (hatCodes w h) e}) :
    (hatExplicitEdgeEquiv w h e).1 = hatLimitEdgeMap w h e.1 := rfl

/-- Ordered endpoint compatibility of the explicit graph equivalences -/
theorem hatExplicitEdgeEquiv_incidence (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (e : {e : ℕ // EdgePresent (hatCodes w h) e}) :
    edgeWest w (hatExplicitEdgeEquiv w h e).1 =
        hatLimitVertexMap w h (edgeWest (hatCodes w h) e.1) ∧
      edgeEast w (hatExplicitEdgeEquiv w h e).1 =
        hatLimitVertexMap w h (edgeEast (hatCodes w h) e.1) := by
  obtain ⟨_, _, _, hw, he⟩ := edge_data (hatLimitExplicitInput w h) e.2
  exact ⟨hw, he⟩

/-- All three local triangle edges are present in the limit graph -/
theorem hatLocalTri_edges_present (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (t : HatLocalTri w h) :
    EdgePresent (hatCodes w h) t.1.1 ∧
      EdgePresent (hatCodes w h) t.1.2.1 ∧ EdgePresent (hatCodes w h) t.1.2.2 := by
  obtain ⟨m, hm⟩ := t.2
  obtain ⟨b1, b2, b3⟩ := triBound_stage (hatCodes w h) m t.1 hm
  exact ⟨hatLocal_allocated_edge_present w h m _ b1,
    hatLocal_allocated_edge_present w h m _ b2,
    hatLocal_allocated_edge_present w h m _ b3⟩

/-- Each component of the face image is the image under the very same graph
edge equivalence, in the stored triple order. This ties the graph and
unoriented face layers of the hatted half of `lem-quad-kmsw`
and planar identification remain; not counted. -/
theorem hatLimitFaceEquiv_compatible (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (t : HatLocalTri w h) :
    (hatLimitFaceEquiv w h t).1 =
      ((hatExplicitEdgeEquiv w h ⟨t.1.1, (hatLocalTri_edges_present w h t).1⟩).1,
       (hatExplicitEdgeEquiv w h ⟨t.1.2.1, (hatLocalTri_edges_present w h t).2.1⟩).1,
       (hatExplicitEdgeEquiv w h ⟨t.1.2.2, (hatLocalTri_edges_present w h t).2.2⟩).1) := rfl

/-- Bundled explicit graph and unoriented face layer of the hatted half of
edge and face equivalences share the same coherent limit maps and preserve
ordered endpoints and stored face components. Rotation, orientation of
faces, hatted-walk identification and planar identification remain; this
helper is not counted as the paper result. -/
theorem hatExplicitGraphFaceIso (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∃ (V : {a : PresentVertex (hatCodes w h) //
          ∃ m, a.id < (kmswStage (hatCodes w h) m).nextVertex} ≃
        {v : PresentVertex w // Reachable (⟨0⟩ : PresentVertex w) v})
      (E : {e : ℕ // EdgePresent (hatCodes w h) e} ≃
        {e : ℕ // EdgePresent w e ∧
          Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ ∧
          Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩})
      (F : HatLocalTri w h ≃ GlobalHatTri w),
      (∀ a, (V a).1.id = hatLimitVertexMap w h a.1.id) ∧
      (∀ e, (E e).1 = hatLimitEdgeMap w h e.1) ∧
      (∀ e, edgeWest w (E e).1 =
          hatLimitVertexMap w h (edgeWest (hatCodes w h) e.1) ∧
        edgeEast w (E e).1 =
          hatLimitVertexMap w h (edgeEast (hatCodes w h) e.1)) ∧
      (∀ t, (F t).1 =
        ((E ⟨t.1.1, (hatLocalTri_edges_present w h t).1⟩).1,
         (E ⟨t.1.2.1, (hatLocalTri_edges_present w h t).2.1⟩).1,
         (E ⟨t.1.2.2, (hatLocalTri_edges_present w h t).2.2⟩).1)) := by
  exact ⟨hatExplicitVertexEquiv w h, hatExplicitEdgeEquiv w h,
    hatLimitFaceEquiv w h, hatExplicitVertexEquiv_apply w h,
    hatExplicitEdgeEquiv_apply w h, hatExplicitEdgeEquiv_incidence w h,
    hatLimitFaceEquiv_compatible w h⟩

end DirectedDistances.KMSW
