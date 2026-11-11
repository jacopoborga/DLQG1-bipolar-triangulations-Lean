module

public import DirectedDistances.KMSW.ActiveTimeMonotone
import DirectedDistances.KMSW.StageFrontier
import DirectedDistances.KMSW.SDPIdentifyBdy
import DirectedDistances.KMSW.BoundaryEnumeration

/-! Supporting lemmas for paper labels `lem-directed-contain`, `lem-infty-cut` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.KMSW

open Quiver






theorem cut_entry_frontier_of_shared_endpoint (w : ℕ → Fin 3)
    {t e f z : ℕ} (he : EdgePresent w e) (hf : EdgePresent w f)
    (het : actTime w e he < t) (hft : t ≤ actTime w f hf)
    (hez : edgeWest w e = z ∨ edgeEast w e = z)
    (hfz : edgeWest w f = z) :
    ∃ g, g ∈ (kmswStage w t).UL ++ (kmswStage w t).UR ∧
      ((kmswStage w t).west g = z ∨ (kmswStage w t).east g = z) := by
  have healloc : e < (kmswStage w t).nextEdge := by
    rw [actTime_spec w e he]
    exact act_lt_nextEdge w het.le
  have heends := edge_endpoints_eq w healloc
  have hebound := kmswStage_endpoints_lt_nextVertex w t e healloc
  have hzbound : z < (kmswStage w t).nextVertex := by
    rcases hez with hz | hz
    · rw [heends.1, hz] at hebound
      exact hebound.1
    · rw [heends.2, hz] at hebound
      exact hebound.2
  have hfuture := (kmswStage_act_endpoint_since w
    (m := actTime w f hf + 1) hft (Nat.lt_succ_self _)).1
  have hfends := edge_endpoints_eq w
    (act_lt_nextEdge w (Nat.le_refl (actTime w f hf)))
  have hwest : (kmswStage w (actTime w f hf)).west
      (act w (actTime w f hf)) = z := by
    rw [hfends.1, ← actTime_spec w f hf, hfz]
  rw [hwest] at hfuture
  rcases hfuture with hfrontier | hfresh
  · exact hfrontier
  · omega

private theorem edge_endpoints_mem_path_vertices {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) {e : ℕ}
    (he : e ∈ pathEdgeList p) :
    (⟨edgeWest w e⟩ : PresentVertex w) ∈ p.vertices ∧
      (⟨edgeEast w e⟩ : PresentVertex w) ∈ p.vertices := by
  induction p with
  | nil => simp [pathEdgeList] at he
  | @cons b c p f ih =>
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hw, ht⟩ := ih he
      exact ⟨(Path.mem_vertices_cons p f).2 (Or.inl hw),
        (Path.mem_vertices_cons p f).2 (Or.inl ht)⟩
    · have hef : e = f.val := List.mem_singleton.mp he
      subst e
      have hw : (⟨edgeWest w f.val⟩ : PresentVertex w) = b := by
        cases b
        exact congrArg PresentVertex.mk f.property.2.1
      have ht : (⟨edgeEast w f.val⟩ : PresentVertex w) = c := by
        cases c
        exact congrArg PresentVertex.mk f.property.2.2
      rw [hw, ht]
      exact ⟨(Path.mem_vertices_cons p f).2 (Or.inl p.end_mem_vertices),
        (p.cons f).end_mem_vertices⟩

private theorem prefix_to_vertex_with_edges {w : ℕ → Fin 3}
    {a b z : PresentVertex w} (p : Path a b) (hz : z ∈ p.vertices) :
    ∃ q : Path a z, ∀ e ∈ pathEdgeList q, e ∈ pathEdgeList p := by
  obtain ⟨q, r, hqr⟩ := p.exists_eq_comp_of_mem_vertices hz
  refine ⟨q, ?_⟩
  intro e he
  rw [hqr, pathEdgeList_comp]
  exact List.mem_append_left _ he





theorem cut_entry_eta_future_path (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (t : ℕ) :
    ∃ b : PresentVertex w, ∃ p : Path
      (⟨(kmswStage w t).west (act w t)⟩ : PresentVertex w) b,
      pathEdgeList p = act w t :: (kmswStage w t).UR ∧
        ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, t ≤ actTime w e he := by
  obtain ⟨b, p, hp, _⟩ := kmswStage_eta_present_path_of_R_unbounded w hR t
  refine ⟨b, p, hp, ?_⟩
  have hactive : EdgePresent w (act w t) := by
    refine ⟨t, act_lt_nextEdge w le_rfl, ?_⟩
    apply (kmswStage_status w t).2.1
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
    rw [hxs]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have htime : actTime w (act w t) hactive = t :=
    (actTime_eq_iff w _ hactive t).2 rfl
  have hpair := pathEdgeList_actTime_pairwise p
  rw [hp] at hpair
  intro e he hep
  rw [hp] at he
  rcases List.mem_cons.mp he with rfl | he
  · exact htime.ge
  · have hlt := (List.pairwise_cons.mp hpair).1 e he hactive hep
    rw [htime] at hlt
    exact hlt.le






theorem cut_entry_east_frontier_reachable (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (t z : ℕ)
    (hz : z = (kmswStage w t).east (act w t) ∨
      ∃ e ∈ (kmswStage w t).UR,
        (kmswStage w t).west e = z ∨ (kmswStage w t).east e = z) :
    ∃ p : Path (⟨(kmswStage w t).west (act w t)⟩ : PresentVertex w) ⟨z⟩,
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, t ≤ actTime w e he := by
  obtain ⟨b, p, hp, hfuture⟩ := cut_entry_eta_future_path w hR t
  have hzmem : (⟨z⟩ : PresentVertex w) ∈ p.vertices := by
    rcases hz with hz | ⟨e, he, hend⟩
    · have hmem : act w t ∈ pathEdgeList p := by rw [hp]; exact List.mem_cons_self
      have heast := (edge_endpoints_mem_path_vertices p hmem).2
      have hends := edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl t))
      rw [← hends.2, ← hz] at heast
      exact heast
    · have hmem : e ∈ pathEdgeList p := by
        rw [hp]
        exact List.mem_cons_of_mem _ he
      have hends := edge_endpoints_eq w
        ((kmswStage_boundary_ids_lt_nextEdge w t).2 e (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr he))))
      obtain ⟨hw, ht⟩ := edge_endpoints_mem_path_vertices p hmem
      rcases hend with hwz | htz
      · rw [← hends.1, hwz] at hw
        exact hw
      · rw [← hends.2, htz] at ht
        exact ht
  obtain ⟨q, hq⟩ := prefix_to_vertex_with_edges p hzmem
  exact ⟨q, fun e he hep => hfuture e (hq e he) hep⟩

private theorem cut_window_upper_left (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) :
    let t := boundaryHitTime w h (-(K : ℤ))
    (kmswStage w t).UL = [act w t] ∧
      (kmswStage w t).west (act w t) = boundaryVertex w h (-(K : ℤ)) := by
  by_cases hK : K = 0
  · subst K
    simp [boundaryHitTime_zero, boundaryVertex_zero, kmswStage, kmswInit, act]
  · have hk : -(K : ℤ) ≤ -1 := by omega
    let t := boundaryHitTime w h (-(K : ℤ))
    have hfind : t = Nat.find (h.leftHit (-(K : ℤ)) hk) := by
      dsimp [t, boundaryHitTime]
      simp only [dite_eq_right (by omega : -(K : ℤ) ≠ 0),
        dite_eq_right (by omega : ¬0 < -(K : ℤ))]
    have hstrict : ∀ j < t, -(K : ℤ) < L w j := by
      intro j hj
      induction j with
      | zero => simp only [L, Finset.sum_range_zero]; omega
      | succ j ih =>
        have hprev := ih (by omega)
        have hnot : L w (j + 1) ≠ -(K : ℤ) := by
          apply Nat.find_min (h.leftHit (-(K : ℤ)) hk)
          rw [← hfind]
          exact hj
        have hsum : L w (j + 1) = L w j +
            (RandomWalk.lazyTwoDimensionalStep (w j)).1 := Finset.sum_range_succ _ _
        have hlow : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w j)).1 := by
          change -1 ≤ ((w j).val : ℤ) - 1
          omega
        omega
    have hhit : L w t = -(K : ℤ) := boundaryHitTime_left_spec w h hk
    have hmin : minL w t = L w t := by
      obtain ⟨i, hi, heq⟩ := runningMin_attained (L w) t
      change minL w t = L w i at heq
      have hle := runningMin_le (L w) t t le_rfl
      change minL w t ≤ L w t at hle
      by_cases hit : i = t
      · simpa only [hit] using heq
      · have hprior := hstrict i (by omega)
        omega
    have hlen : (kmswStage w t).UL.length = 1 := by
      have hlenZ := kmswStage_UL_length w t
      rw [hmin] at hlenZ
      omega
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
    have hxslen : xs.length = 0 := by
      rw [hxs, List.length_append] at hlen
      simp only [List.length_singleton] at hlen
      omega
    have hUL : (kmswStage w t).UL = [act w t] := by
      rw [hxs, List.length_eq_zero_iff.mp hxslen]
      rfl
    exact ⟨hUL, (CutConverse.activeInitial_eq w t).symm.trans
      (boundaryVertex_left_hit_eq w h hk).symm⟩

private theorem cut_boundary_R_unbounded {w : ℕ → Fin 3}
    (h : BoundaryHitWitnesses w) : ∀ a : ℤ, ∃ m, R w m ≤ a := by
  intro a
  obtain ⟨m, hm⟩ := h.rightHit (max 1 (-a)) (le_max_left _ _)
  refine ⟨m, ?_⟩
  have hk := le_max_right (1 : ℤ) (-a)
  omega







theorem cut_entry_window_east_frontier_reachable (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K z : ℕ)
    (hz : let t := boundaryHitTime w h (-(K : ℤ))
      z = (kmswStage w t).east (act w t) ∨
        ∃ e ∈ (kmswStage w t).UR,
          (kmswStage w t).west e = z ∨ (kmswStage w t).east e = z) :
    ∃ p : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) ⟨z⟩,
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
        boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he := by
  have hroot := (cut_window_upper_left w h K).2
  have hp := cut_entry_east_frontier_reachable w (cut_boundary_R_unbounded h)
    (boundaryHitTime w h (-(K : ℤ))) z hz
  rw [hroot] at hp
  exact hp







theorem cut_entry_window_shared_endpoint_reachable (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) {e f z : ℕ}
    (he : EdgePresent w e) (hf : EdgePresent w f)
    (het : actTime w e he < boundaryHitTime w h (-(K : ℤ)))
    (hft : boundaryHitTime w h (-(K : ℤ)) ≤ actTime w f hf)
    (hez : edgeWest w e = z ∨ edgeEast w e = z) (hfz : edgeWest w f = z) :
    (z = boundaryVertex w h (-(K : ℤ)) ∨
      let t := boundaryHitTime w h (-(K : ℤ))
      z = (kmswStage w t).east (act w t) ∨
        ∃ g ∈ (kmswStage w t).UR,
          (kmswStage w t).west g = z ∨ (kmswStage w t).east g = z) ∧
    ∃ p : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) ⟨z⟩,
      ∀ g ∈ pathEdgeList p, ∀ hg : EdgePresent w g,
        boundaryHitTime w h (-(K : ℤ)) ≤ actTime w g hg := by
  obtain ⟨g, hg, hgend⟩ := cut_entry_frontier_of_shared_endpoint w he hf het hft hez hfz
  obtain ⟨hUL, hroot⟩ := cut_window_upper_left w h K
  have hz : z = boundaryVertex w h (-(K : ℤ)) ∨
      z = (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).east
        (act w (boundaryHitTime w h (-(K : ℤ)))) ∨
      ∃ g ∈ (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).UR,
        (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).west g = z ∨
        (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).east g = z := by
    rcases List.mem_append.mp hg with hg | hg
    · rw [hUL] at hg
      have hgeq := List.mem_singleton.mp hg
      subst g
      rcases hgend with hw | ht
      · exact Or.inl (hw.symm.trans hroot)
      · exact Or.inr (Or.inl ht.symm)
    · exact Or.inr (Or.inr ⟨g, hg, hgend⟩)
  refine ⟨hz, ?_⟩
  rcases hz with hz | hz
  · rw [hz]
    refine ⟨Path.nil, ?_⟩
    intro g hg
    simp only [pathEdgeList, List.not_mem_nil] at hg
  · exact cut_entry_window_east_frontier_reachable w h K z hz

private theorem cut_old_future_initial_reachable (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K z : ℕ) {f : ℕ}
    (hf : EdgePresent w f)
    (hft : boundaryHitTime w h (-(K : ℤ)) ≤ actTime w f hf)
    (hfz : edgeWest w f = z)
    (hz : z < (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).nextVertex) :
    ∃ p : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) ⟨z⟩,
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
        boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he := by
  have hfuture := (kmswStage_act_endpoint_since w
    (m := actTime w f hf + 1) hft (Nat.lt_succ_self _)).1
  have hfends := edge_endpoints_eq w
    (act_lt_nextEdge w (Nat.le_refl (actTime w f hf)))
  have hwest : (kmswStage w (actTime w f hf)).west
      (act w (actTime w f hf)) = z := by
    rw [hfends.1, ← actTime_spec w f hf, hfz]
  rw [hwest] at hfuture
  obtain ⟨g, hg, hgend⟩ := hfuture.resolve_right (by omega)
  obtain ⟨hUL, hroot⟩ := cut_window_upper_left w h K
  rcases List.mem_append.mp hg with hg | hg
  · rw [hUL] at hg
    have hgeq := List.mem_singleton.mp hg
    subst g
    rcases hgend with hw | ht
    · have hzroot := hw.symm.trans hroot
      rw [hzroot]
      refine ⟨Path.nil, ?_⟩
      intro e he
      simp only [pathEdgeList, List.not_mem_nil] at he
    · exact cut_entry_window_east_frontier_reachable w h K z (Or.inl ht.symm)
  · exact cut_entry_window_east_frontier_reachable w h K z (Or.inr ⟨g, hg, hgend⟩)

private theorem cut_after_old_start_reachable (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) {a b : PresentVertex w}
    (ha : a.id < (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).nextVertex)
    (p : Path a b) {f : ℕ} (hf : EdgePresent w f)
    (hfz : edgeWest w f = b.id)
    (hft : boundaryHitTime w h (-(K : ℤ)) ≤ actTime w f hf) :
    ∃ q : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) b,
      ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
        boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he := by
  induction p generalizing f with
  | nil => exact cut_old_future_initial_reachable w h K a.id hf hft hfz ha
  | @cons b c p e ih =>
    by_cases hearly : actTime w e.val e.property.1 < boundaryHitTime w h (-(K : ℤ))
    · exact (cut_entry_window_shared_endpoint_reachable w h K e.property.1 hf
        hearly hft (Or.inr e.property.2.2) hfz).2
    · have het : boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e.val e.property.1 :=
        Nat.le_of_not_gt hearly
      obtain ⟨q, hq⟩ := ih e.property.1 e.property.2.1 het
      refine ⟨q.cons e, ?_⟩
      intro g hg hgp
      rcases List.mem_append.mp hg with hg | hg
      · exact hq g hg hgp
      · have hge : g = e.val := List.mem_singleton.mp hg
        subst g
        exact het

private theorem cut_nonpositive_start_old (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) (k : ℤ)
    (hklo : -(K : ℤ) ≤ k) (hkhi : k ≤ 0) :
    boundaryVertex w h k <
      (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).nextVertex := by
  by_cases hkzero : k = 0
  · subst k
    rw [boundaryVertex_zero]
    have hmono := CutConverse.nextVertex_mono w
      (Nat.zero_le (boundaryHitTime w h (-(K : ℤ))))
    change 2 ≤ _ at hmono
    omega
  · have hk : k ≤ -1 := by omega
    have hfind : boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
      unfold boundaryHitTime
      simp only [dite_eq_right hkzero, dite_eq_right (by omega : ¬0 < k)]
    have hstrict : ∀ j < boundaryHitTime w h k, k < L w j := by
      intro j hj
      induction j with
      | zero => simp only [L, Finset.sum_range_zero]; omega
      | succ j ih =>
        have hprev := ih (by omega)
        have hnot : L w (j + 1) ≠ k := by
          apply Nat.find_min (h.leftHit k hk)
          rw [← hfind]
          exact hj
        have hsum : L w (j + 1) = L w j +
            (RandomWalk.lazyTwoDimensionalStep (w j)).1 := Finset.sum_range_succ _ _
        have hlow : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w j)).1 := by
          change -1 ≤ ((w j).val : ℤ) - 1
          omega
        omega
    have htime : boundaryHitTime w h k ≤ boundaryHitTime w h (-(K : ℤ)) := by
      by_contra hn
      have hbefore := hstrict _ (Nat.lt_of_not_ge hn)
      have hKpos : -(K : ℤ) ≤ -1 := by omega
      have hhit := boundaryHitTime_left_spec w h hKpos
      omega
    have he := act_lt_nextEdge w htime
    have hbound := (kmswStage_endpoints_lt_nextVertex w _ _ he).1
    rw [(edge_endpoints_eq w he).1] at hbound
    rw [boundaryVertex_left_hit_eq w h hk]
    exact hbound

private theorem cut_nonnegative_boundary_path (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (n : ℕ) :
    Nonempty (Path (⟨boundaryVertex w h 0⟩ : PresentVertex w)
      ⟨boundaryVertex w h (n : ℤ)⟩) := by
  induction n with
  | zero => exact ⟨Path.nil⟩
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      have hp : EdgePresent w 0 := ⟨0, Nat.zero_lt_one, rfl⟩
      let e : (⟨boundaryVertex w h 0⟩ : PresentVertex w) ⟶
          ⟨boundaryVertex w h 1⟩ :=
        ⟨0, hp, by rw [boundaryVertex_zero]; rfl,
          by rw [boundaryVertex_one]; rfl⟩
      exact ⟨e.toPath⟩
    · obtain ⟨N, hN, hright⟩ := boundaryVertex_right_edge w h
        (k := (n : ℤ)) (by omega)
      have hs := hright N le_rfl
      have he := act_lt_nextEdge w hN
      have hp : EdgePresent w (act w (boundaryHitTime w h (n : ℤ))) :=
        ⟨N, he, hs.2.1⟩
      have hw : edgeWest w (act w (boundaryHitTime w h (n : ℤ))) =
          boundaryVertex w h (n : ℤ) := (edge_endpoints_eq w he).1.symm.trans hs.2.2.1
      have ht : edgeEast w (act w (boundaryHitTime w h (n : ℤ))) =
          boundaryVertex w h ((n + 1 : ℕ) : ℤ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (edge_endpoints_eq w he).2.symm.trans hs.2.2.2
      obtain ⟨p⟩ := ih
      exact ⟨p.cons ⟨_, hp, hw, ht⟩⟩

private theorem cut_window_prefix_endpoint_reachable (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) (k : ℤ) (hk : -(K : ℤ) ≤ k)
    {b : PresentVertex w}
    (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) b)
    {f : ℕ} (hf : EdgePresent w f) (hfz : edgeWest w f = b.id)
    (hft : boundaryHitTime w h (-(K : ℤ)) ≤ actTime w f hf) :
    ∃ q : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) b,
      ∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
        boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he := by
  by_cases hkhi : k ≤ 0
  · exact cut_after_old_start_reachable w h K
      (cut_nonpositive_start_old w h K k hk hkhi) p hf hfz hft
  · obtain ⟨r⟩ := cut_nonnegative_boundary_path w h k.toNat
    have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
    rw [hkcast] at r
    have hrootold := cut_nonpositive_start_old w h K 0 (by omega) le_rfl
    exact cut_after_old_start_reachable w h K hrootold (r.comp p) hf hfz hft











theorem cut_entry_window_future_suffix (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) :
    let t := boundaryHitTime w h (-(K : ℤ))
    let E : Set (PresentVertex w) :=
      (fun n => (⟨n⟩ : PresentVertex w)) '' Set.Iio (kmswStage w t).nextVertex ∪
        (fun k => (⟨boundaryVertex w h k⟩ : PresentVertex w)) ''
          Set.Icc (-(K : ℤ)) (K : ℤ)
    let A : Set (PresentVertex w) := {z | z ∈ E ∧
      ∃ r : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) z,
        ∀ e ∈ pathEdgeList r, ∀ he : EdgePresent w e, t ≤ actTime w e he}
    E.Finite ∧ A.Finite ∧ ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
      ∀ {v} (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
        v ∈ E ∨ ∃ z ∈ A, ∃ q : Path z v,
          (∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e, t ≤ actTime w e he) ∧
            ∀ y ∈ q.vertices, y ∈ p.vertices := by
  let t := boundaryHitTime w h (-(K : ℤ))
  let E : Set (PresentVertex w) :=
    (fun n => (⟨n⟩ : PresentVertex w)) '' Set.Iio (kmswStage w t).nextVertex ∪
      (fun k => (⟨boundaryVertex w h k⟩ : PresentVertex w)) ''
        Set.Icc (-(K : ℤ)) (K : ℤ)
  let A : Set (PresentVertex w) := {z | z ∈ E ∧
    ∃ r : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) z,
      ∀ e ∈ pathEdgeList r, ∀ he : EdgePresent w e, t ≤ actTime w e he}
  have hE : E.Finite := ((Set.finite_Iio _).image _).union
    ((Set.finite_Icc _ _).image _)
  refine ⟨hE, hE.subset (fun _ hz => hz.1), ?_⟩
  intro k hklo hkhi v p
  induction p with
  | nil => exact Or.inl (Or.inr ⟨k, ⟨hklo, hkhi⟩, rfl⟩)
  | @cons b c p e ih =>
    by_cases hearly : actTime w e.val e.property.1 < t
    · have healloc : e.val < (kmswStage w t).nextEdge := by
        rw [actTime_spec w e.val e.property.1]
        exact act_lt_nextEdge w hearly.le
      have hc := (kmswStage_endpoints_lt_nextVertex w t e.val healloc).2
      rw [(edge_endpoints_eq w healloc).2, e.property.2.2] at hc
      exact Or.inl (Or.inl ⟨c.id, hc, by cases c; rfl⟩)
    · have het : t ≤ actTime w e.val e.property.1 := Nat.le_of_not_gt hearly
      rcases ih with hb | ⟨z, hz, q, hq, hvertices⟩
      · obtain ⟨r, hr⟩ := cut_window_prefix_endpoint_reachable w h K k hklo p
          e.property.1 e.property.2.1 het
        refine Or.inr ⟨b, ⟨hb, r, hr⟩, e.toPath, ?_, ?_⟩
        · intro f hf hfp
          have hfe : f = e.val := by
            simpa only [Hom.toPath, pathEdgeList, List.nil_append,
              List.mem_singleton] using hf
          subst f
          exact het
        · intro y hy
          rcases (Path.mem_vertices_cons Path.nil e).1 hy with hy | hy
          · have hyb : y = b := List.mem_singleton.mp hy
            rw [hyb]
            exact (Path.mem_vertices_cons p e).2 (Or.inl p.end_mem_vertices)
          · exact (Path.mem_vertices_cons p e).2 (Or.inr hy)
      · refine Or.inr ⟨z, hz, q.cons e, ?_, ?_⟩
        · intro f hf hfp
          rcases List.mem_append.mp hf with hf | hf
          · exact hq f hf hfp
          · have hfe : f = e.val := List.mem_singleton.mp hf
            subst f
            exact het
        · intro y hy
          rcases (Path.mem_vertices_cons q e).1 hy with hy | hy
          · exact (Path.mem_vertices_cons p e).2 (Or.inl (hvertices y hy))
          · exact (Path.mem_vertices_cons p e).2 (Or.inr hy)

end DirectedDistances.KMSW
