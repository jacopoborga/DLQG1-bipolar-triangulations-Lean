module

public import DirectedDistances.PaperProofs.Section7.LongPathFirstExit
public import DirectedDistances.PaperProofs.Section7.LongPathStageVertices
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
import DirectedDistances.KMSW.RunBoundaryVertexLabels
import DirectedDistances.KMSW.StageFrontier
import DirectedDistances.KMSW.ActiveTimeMonotone








public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem stage_LL_mem_mono (w : ℕ → Fin 3) {n m e : ℕ}
    (hnm : n ≤ m) (he : e ∈ (kmswStage w n).LL) :
    e ∈ (kmswStage w m).LL := by
  induction m, hnm using Nat.le_induction with
  | base => exact he
  | succ m _ ih =>
    change e ∈ (kmswStep (kmswStage w m) (w m)).LL
    unfold kmswStep
    cases kmswCodeStep (w m) with
    | down =>
      cases hs : (kmswStage w m).UR <;>
        simpa only [kmswStepOfStep, hs, State.addEdge] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w m).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil =>
        simpa only [kmswStepOfStep, hs, State.addEdge, List.mem_cons] using
          (Or.inr ih)

private theorem present_edge_not_LL (w : ℕ → Fin 3) {n e : ℕ}
    (he : EdgePresent w e) : e ∉ (kmswStage w n).LL := by
  intro hLL
  obtain ⟨m, hm⟩ := he.eventually_present
  let N := max n m
  have hmem := stage_LL_mem_mono w (Nat.le_max_left n m) hLL
  have hp := hm N (Nat.le_max_right n m)
  have hf := ((kmswStage_status w N).1 e hp.1).mpr (Or.inr hmem)
  rw [hf] at hp
  exact Bool.noConfusion hp.2

private theorem exit_edge_activation_late (w : ℕ → Fin 3) {n e : ℕ}
    (he : EdgePresent w e)
    (hExit : ¬ (e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true)) :
    n < actTime w e he := by
  by_contra hnot
  have hle : actTime w e he ≤ n := by omega
  let t := actTime w e he
  have halloc : e < (kmswStage w t).nextEdge := by
    rw [actTime_spec w e he]
    exact act_lt_nextEdge w le_rfl
  have hp : (kmswStage w t).present e = true := by
    rw [actTime_spec w e he]
    apply (kmswStage_status w (actTime w e he)).2.1
    obtain ⟨es, hes⟩ := kmswStage_UL_last w (actTime w e he)
    rw [hes]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  exact hExit (present_mono w halloc hp n hle)





theorem first_unpresent_edge_status (w : ℕ → Fin 3) {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (n T : ℕ)
    (hExit : ¬ (P.edge T < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present (P.edge T) = true)) :
    (kmswStage w n).nextEdge ≤ P.edge T ∨
      (P.edge T < (kmswStage w n).nextEdge ∧
        P.edge T ∈ (kmswStage w n).UR ∧
        (kmswStage w n).present (P.edge T) = false ∧
        P.edge T ∉ (kmswStage w n).LL) := by
  have hnotLL := present_edge_not_LL w (n := n) (P.edge_outgoing_at_initial w T).1
  by_cases ha : P.edge T < (kmswStage w n).nextEdge
  · have hp : (kmswStage w n).present (P.edge T) = false := by
      cases hs : (kmswStage w n).present (P.edge T) with
      | false => rfl
      | true => exact False.elim (hExit ⟨ha, hs⟩)
    have hmissing := ((kmswStage_status w n).1 (P.edge T) ha).mp hp
    exact Or.inr ⟨ha, hmissing.resolve_right hnotLL, hp, hnotLL⟩
  · exact Or.inl (by omega)





theorem first_unpresent_edge_upper_boundary (w : ℕ → Fin 3) {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (n T : ℕ)
    (hv : v < (kmswStage w n).nextVertex)
    (hExit : ¬ (P.edge T < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present (P.edge T) = true))
    (hBefore : ∀ t, t < T → P.edge t < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present (P.edge t) = true) :
    ∃ e, e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ∧
      ((kmswStage w n).west e = (P.initial T).1.id ∨
        (kmswStage w n).east e = (P.initial T).1.id) := by
  have hz : (P.initial T).1.id < (kmswStage w n).nextVertex := by
    cases T with
    | zero =>
      have heq := Path.eq_of_length_zero (P.initial 0).2 (P.prefix_length 0)
      have hid := congrArg PresentVertex.id heq
      exact hid ▸ hv
    | succ t =>
      have ha := (hBefore t (Nat.lt_succ_self t)).1
      have hb := (kmswStage_endpoints_lt_nextVertex w n (P.edge t) ha).2
      rw [(edge_endpoints_eq w ha).2,
        (P.edge_incoming_at_succ w t).2] at hb
      exact hb
  have he := (P.edge_outgoing_at_initial w T).1
  have hlate := exit_edge_activation_late w he hExit
  have hfrontier := (kmswStage_act_endpoint_since w
    (m := actTime w (P.edge T) he + 1) hlate.le (Nat.lt_succ_self _)).1
  have ha := act_lt_nextEdge w (Nat.le_refl (actTime w (P.edge T) he))
  rw [(edge_endpoints_eq w ha).1, ← actTime_spec w (P.edge T) he,
    (P.edge_outgoing_at_initial w T).2] at hfrontier
  exact hfrontier.resolve_right (by omega)

private theorem left_hit_strict (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (k : ℕ) (hk : 0 < k) :
    ∀ j < boundaryHitTime w h (-(k : ℤ)), -(k : ℤ) < L w j := by
  have hkneg : -(k : ℤ) ≤ -1 := by omega
  have hfind : boundaryHitTime w h (-(k : ℤ)) =
      Nat.find (h.leftHit (-(k : ℤ)) hkneg) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : -(k : ℤ) ≠ 0),
      dite_eq_right (by omega : ¬0 < -(k : ℤ))]
  intro j hj
  induction j with
  | zero => simp only [L, Finset.sum_range_zero]; omega
  | succ j ih =>
    have hprev := ih (by omega)
    have hnot : L w (j + 1) ≠ -(k : ℤ) := by
      apply Nat.find_min (h.leftHit (-(k : ℤ)) hkneg)
      rw [← hfind]
      exact hj
    have hsum : L w (j + 1) = L w j +
        (RandomWalk.lazyTwoDimensionalStep (w j)).1 := Finset.sum_range_succ _ _
    have hlow : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w j)).1 := by
      change -1 ≤ ((w j).val : ℤ) - 1
      omega
    omega

private theorem left_hit_UL_singleton (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (k : ℕ) (hk : 0 < k) :
    let n := boundaryHitTime w h (-(k : ℤ))
    (kmswStage w n).UL = [act w n] := by
  let n := boundaryHitTime w h (-(k : ℤ))
  have hhit : L w n = -(k : ℤ) := boundaryHitTime_left_spec w h (by omega)
  have hmin : minL w n = L w n := by
    obtain ⟨i, hi, heq⟩ := runningMin_attained (L w) n
    change minL w n = L w i at heq
    have hle := runningMin_le (L w) n n le_rfl
    change minL w n ≤ L w n at hle
    by_cases hin : i = n
    · simpa only [hin] using heq
    · have hprior := left_hit_strict w h k hk i (by omega)
      omega
  have hlen : (kmswStage w n).UL.length = 1 := by
    have hlenZ := kmswStage_UL_length w n
    rw [hmin] at hlenZ
    omega
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hxslen : xs.length = 0 := by
    rw [hxs, List.length_append] at hlen
    simp only [List.length_singleton] at hlen
    omega
  change (kmswStage w n).UL = [act w n]
  rw [hxs, List.length_eq_zero_iff.mp hxslen]
  rfl






theorem first_unpresent_edge_at_left_hit (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (ell k : ℕ) (hlt : ell < k)
    (P : InfinitePresentPath w ⟨boundaryVertex w h (-(ell : ℤ))⟩) :
    let n := boundaryHitTime w h (-(k : ℤ))
    ∃ T, ¬ (P.edge T < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge T) = true) ∧
      (∀ t, t < T → P.edge t < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge t) = true) ∧
      ((kmswStage w n).nextEdge ≤ P.edge T ∨
        (P.edge T < (kmswStage w n).nextEdge ∧
          P.edge T ∈ (kmswStage w n).UR ∧
          (kmswStage w n).present (P.edge T) = false ∧
          P.edge T ∉ (kmswStage w n).LL)) ∧
      (∃ e, e ∈ act w n :: (kmswStage w n).UR ∧
        ((kmswStage w n).west e = (P.initial T).1.id ∨
          (kmswStage w n).east e = (P.initial T).1.id)) := by
  let n := boundaryHitTime w h (-(k : ℤ))
  have hn : boundaryHitTime w h (-(ell : ℤ)) ≤ n := by
    by_cases hell : ell = 0
    · simp only [hell, Nat.cast_zero, neg_zero, boundaryHitTime_zero]
      exact Nat.zero_le _
    · by_contra hnot
      have hs := left_hit_strict w h ell (by omega) n (by omega)
      have hkHit : L w n = -(k : ℤ) := boundaryHitTime_left_spec w h (by omega)
      omega
  have hv := boundaryVertex_lt_stageNextVertex w h (-(ell : ℤ)) n hn
  obtain ⟨T, hExit, hBefore⟩ := first_unpresent_edge w P n
  have hstatus := first_unpresent_edge_status w P n T hExit
  obtain ⟨e, he, hends⟩ := first_unpresent_edge_upper_boundary w P n T hv hExit hBefore
  have hUL := left_hit_UL_singleton w h k (by omega)
  change (kmswStage w n).UL = [act w n] at hUL
  rw [hUL, List.singleton_append] at he
  exact ⟨T, hExit, hBefore, hstatus, e, he, hends⟩


private theorem upper_right_edge_future_LR (w : ℕ → Fin 3) (n : ℕ)
    (hFuture : BoundaryHitWitnesses (fun i => w (n + i))) (e : ℕ)
    (he : e ∈ act w n :: (kmswStage w n).UR) :
    ∃ m f, f < (kmswStage (fun i => w (n + i)) m).nextEdge ∧
      f ∈ (kmswStage (fun i => w (n + i)) m).LR ∧
      kmswWindowEdgeMapInf w n f = e := by
  rcases List.mem_cons.mp he with he | he
  · subst e
    refine ⟨0, 0, by change 0 < 1; omega, by simp [kmswStage, kmswInit], ?_⟩
    rw [kmswWindowEdgeMapInf_eq_stage w n 0 0 (by change 0 < 1; omega)]
    rfl
  · let u := fun i => w (n + i)
    let K := (kmswStage w n).UR.length + 1
    obtain ⟨m, hm⟩ := hFuture.rightHit (K : ℤ) (by dsimp [K]; omega)
    have hr := kmswWindowPatchData_rel w n m
    let d := kmswWindowPatchData w n m
    change KMSWWindowPatchRel (kmswStage w n) (kmswStage w (n + m))
      (kmswStage u m) d.φ d.A d.B d.YL d.YR d.XL d.XR at hr
    have hB : d.B = [] := by
      by_contra hB
      have hXR : d.XR = [] := hr.xr_nil hB
      have hres := congrArg List.length hr.right_residual
      have hlr := congrArg List.length hr.lr_split
      change (kmswStage u m).LR.length = ([0] ++ d.YR ++ d.XR).length at hlr
      rw [hXR] at hlr
      simp only [List.length_append, List.length_singleton, List.length_nil,
        Nat.add_zero, List.length_map] at hres hlr
      have hlen := kmswStage_LR_length u m
      have hmin := runningMin_le (R u) m m le_rfl
      change minR u m ≤ R u m at hmin
      change R u m = -(K : ℤ) at hm
      dsimp only [K] at hm
      omega
    have hres : (kmswStage w n).UR = d.YR.map d.φ := by
      simpa only [hB, List.append_nil] using hr.right_residual
    rw [hres] at he
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
    have hfLR : f ∈ (kmswStage u m).LR := by
      rw [hr.lr_split]
      exact List.mem_append_left _ (List.mem_append_right _ hf)
    have halloc := (kmswStage_boundary_ids_lt_nextEdge u m).2 f
      (List.mem_append_right _ hfLR)
    refine ⟨m, f, halloc, hfLR, ?_⟩
    rw [kmswWindowEdgeMapInf_eq_stage w n m f halloc]
    exact hfe

private theorem finite_LR_eq_right_boundary (u : ℕ → Fin 3) (m f : ℕ)
    (hf : f ∈ (kmswStage u m).LR) :
    ∃ j : ℕ, f = kmswRightBoundaryEdge u j := by
  classical
  rw [kmswStage_LR_eq] at hf
  obtain ⟨t, ht, htf⟩ := List.mem_map.mp hf
  have hrecord : ∀ i, i < t → R u t < R u i :=
    of_decide_eq_true (List.mem_filter.mp ht).2
  refine ⟨Nat.count (fun t => ∀ i, i < t → R u t < R u i) t, ?_⟩
  unfold kmswRightBoundaryEdge
  rw [natSelect_count hrecord]
  exact htf.symm






theorem upper_right_endpoint_future_boundary (w : ℕ → Fin 3) (n : ℕ)
    (hFuture : BoundaryHitWitnesses (fun i => w (n + i))) (e v : ℕ)
    (he : e ∈ act w n :: (kmswStage w n).UR)
    (hv : (kmswStage w n).west e = v ∨ (kmswStage w n).east e = v) :
    ∃ j : ℕ, v = kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hFuture (j : ℤ)) := by
  let u := fun i => w (n + i)
  obtain ⟨m, f, hf, hfLR, hfe⟩ := upper_right_edge_future_LR w n hFuture e he
  obtain ⟨j, hfj⟩ := finite_LR_eq_right_boundary u m f hfLR
  have healloc : e < (kmswStage w n).nextEdge := by
    rcases List.mem_cons.mp he with he | he
    · rw [he]
      exact act_lt_nextEdge w le_rfl
    · exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e
        (by simp only [List.mem_append]; tauto)
  have hstable := kmswStage_endpoints_stable w (Nat.le_add_right n m) healloc
  have hlocal := edge_endpoints_eq u hf
  have hlabels := kmswRightBoundaryEdge_hit_endpoints u hFuture j
  rcases hv with hv | hv
  · refine ⟨j, ?_⟩
    calc
      v = (kmswStage w n).west e := hv.symm
      _ = (kmswStage w (n + m)).west e := hstable.1.symm
      _ = kmswWindowVertexMapInf w n ((kmswStage u m).west f) := by
        rw [← hfe]
        exact kmswWindowEdgeMapInf_west w n m f hf
      _ = kmswWindowVertexMapInf w n (boundaryVertex u hFuture (j : ℤ)) := by
        rw [hlocal.1, hfj, hlabels.1]
  · refine ⟨j + 1, ?_⟩
    calc
      v = (kmswStage w n).east e := hv.symm
      _ = (kmswStage w (n + m)).east e := hstable.2.symm
      _ = kmswWindowVertexMapInf w n ((kmswStage u m).east f) := by
        rw [← hfe]
        exact kmswWindowEdgeMapInf_east w n m f hf
      _ = kmswWindowVertexMapInf w n
          (boundaryVertex u hFuture ((j + 1 : ℕ) : ℤ)) := by
        rw [hlocal.2, hfj, hlabels.2, Nat.cast_add, Nat.cast_one]





theorem first_unpresent_edge_future_boundary (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (ell k : ℕ) (hlt : ell < k)
    (P : InfinitePresentPath w ⟨boundaryVertex w h (-(ell : ℤ))⟩)
    (hFuture : BoundaryHitWitnesses
      (fun i => w (boundaryHitTime w h (-(k : ℤ)) + i))) :
    let n := boundaryHitTime w h (-(k : ℤ))
    ∃ T, ¬ (P.edge T < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge T) = true) ∧
      (∀ t, t < T → P.edge t < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge t) = true) ∧
      ∃ j : ℕ, (P.initial T).1.id = kmswWindowVertexMapInf w n
        (boundaryVertex (fun i => w (n + i)) hFuture (j : ℤ)) := by
  let n := boundaryHitTime w h (-(k : ℤ))
  obtain ⟨T, hExit, hBefore, _, e, he, hends⟩ :=
    first_unpresent_edge_at_left_hit w h ell k hlt P
  exact ⟨T, hExit, hBefore,
    upper_right_endpoint_future_boundary w n hFuture e (P.initial T).1.id he hends⟩

end DirectedDistances.PaperProofs.Section7
