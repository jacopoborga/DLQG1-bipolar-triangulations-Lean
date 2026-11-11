module

public import DirectedDistances.KMSW.UIBHBOTRotationHypothesis
public import DirectedDistances.KMSW.KMSWWindowEventualCaptureH
public import DirectedDistances.KMSW.KMSWWindowCaptureEventRel
import DirectedDistances.KMSW.AllocatedVertices
import DirectedDistances.RandomWalk.UIBHBOTForwardUnbounded

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem windowEdgeMapInf_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem wholePlaneEdgeTrans_act (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M)
    (k : ℕ) :
    wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
    windowEdgeMapInf_act (shiftedStream W M) (M - N) k

private def absoluteActiveEdge (W : ℤ → Fin 3) (t : ℤ) : WholePlaneEdge W :=
  wholePlaneEdgeι W (-t).toNat
    (act (shiftedStream W (-t).toNat) (t + ((-t).toNat : ℤ)).toNat)

private theorem absoluteActiveEdge_eq (W : ℤ → Fin 3) (N k : ℕ) :
    absoluteActiveEdge W ((k : ℤ) - N) =
      wholePlaneEdgeι W N (act (shiftedStream W N) k) := by
  unfold absoluteActiveEdge
  apply Quotient.sound
  let A := (-((k : ℤ) - N)).toNat
  refine ⟨max A N, Nat.le_max_left _ _, Nat.le_max_right _ _, ?_⟩
  change wholePlaneEdgeTrans W A (max A N) _
      (act (shiftedStream W A) ((k : ℤ) - N + (A : ℤ)).toNat) =
    wholePlaneEdgeTrans W N (max A N) _ (act (shiftedStream W N) k)
  rw [wholePlaneEdgeTrans_act, wholePlaneEdgeTrans_act]
  congr 1
  dsimp only [A]
  omega

private theorem absoluteActiveEdge_injective (W : ℤ → Fin 3) :
    Function.Injective (absoluteActiveEdge W) := by
  intro t u he
  obtain ⟨M, ht, hu, h⟩ := Quotient.exact he
  change wholePlaneEdgeTrans W (-t).toNat M ht
      (act (shiftedStream W (-t).toNat) (t + ((-t).toNat : ℤ)).toNat) =
    wholePlaneEdgeTrans W (-u).toNat M hu
      (act (shiftedStream W (-u).toNat) (u + ((-u).toNat : ℤ)).toNat) at h
  rw [wholePlaneEdgeTrans_act, wholePlaneEdgeTrans_act] at h
  have hk := CutConverse.act_injective (shiftedStream W M) h
  change (-t).toNat ≤ M at ht
  change (-u).toNat ≤ M at hu
  change M - (-t).toNat + (t + ((-t).toNat : ℤ)).toNat =
    M - (-u).toNat + (u + ((-u).toNat : ℤ)).toNat at hk
  omega

private theorem incident_active_time_lower_bound (W : ℤ → Fin 3)
    (V : WholePlaneVertex W)
    (hfin : {e : WholePlaneEdge W |
      wholePlaneEdgeWest W e = V ∨ wholePlaneEdgeEast W e = V}.Finite) :
    ∃ b : ℤ, ∀ M k : ℕ,
      (wholePlaneVertexι W M ((kmswStage (shiftedStream W M) k).west
          (act (shiftedStream W M) k)) = V ∨
        wholePlaneVertexι W M ((kmswStage (shiftedStream W M) k).east
          (act (shiftedStream W M) k)) = V) → b ≤ (k : ℤ) - M := by
  have hf := hfin.preimage (absoluteActiveEdge_injective W).injOn
  obtain ⟨b, hb⟩ := hf.bddBelow
  refine ⟨b, ?_⟩
  intro M k hk
  apply hb
  change wholePlaneEdgeWest W (absoluteActiveEdge W ((k : ℤ) - M)) = V ∨
    wholePlaneEdgeEast W (absoluteActiveEdge W ((k : ℤ) - M)) = V
  rw [absoluteActiveEdge_eq, wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι]
  have he := edge_endpoints_eq (shiftedStream W M)
    (kmswStage_boundary_ids_lt_nextEdge (shiftedStream W M) k).1
  simpa only [act, he.1, he.2] using hk

private theorem vertex_eventually_down_nonrecord (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k))
    (N v : ℕ) :
    ∃ A, ∃ hNA : N ≤ A, ∀ M (hAM : A ≤ M),
      2 ≤ wholePlaneVertexTrans W N M (hNA.trans hAM) v ∧
      ∀ k, wholePlaneVertexTrans W N M (hNA.trans hAM) v =
        (kmswStage (shiftedStream W M) k).nextVertex →
        kmswCodeStep (shiftedStream W M k) = .down →
          (kmswStage (shiftedStream W M) k).UR ≠ [] := by
  classical
  obtain ⟨b, hb⟩ := incident_active_time_lower_bound W (wholePlaneVertexι W N v)
    (wholePlane_incidentEdges_finite W H (wholePlaneVertexι W N v))
  obtain ⟨J, hJ⟩ := kmsw_vertex_allocated_of_finite_incidence
    (shiftedStream W N) (H.1 N) v
  let s := Finset.Icc (b - 1) ((J : ℤ) - N)
  let f : ℤ → ℕ := fun t => Classical.choose (hB t)
  let A := max N (max (s.sup f) (-b + 1).toNat)
  have hNA : N ≤ A := by dsimp only [A]; omega
  refine ⟨A, hNA, ?_⟩
  intro M hAM
  have hNM : N ≤ M := hNA.trans hAM
  have hsup : s.sup f ≤ M := by dsimp only [A] at hAM; omega
  have hMb : -b + 1 ≤ (M : ℤ) := by dsimp only [A] at hAM; omega
  let u := wholePlaneVertexTrans W N M hNM v
  have hι : wholePlaneVertexι W M u = wholePlaneVertexι W N v :=
    congrFun (wholePlaneVertexι_trans W N M hNM) v
  have huBound : u < (kmswStage (shiftedStream W M) (M - N + J)).nextVertex := by
    have hv : v < (kmswStage (fun i => shiftedStream W M (M - N + i)) J).nextVertex := by
      rw [shiftedStream_shift W N M hNM]
      exact hJ
    have hm := (kmswWindowPatchVertexMap_rel (shiftedStream W M) (M - N) J).vertex_bound
      v hv
    rw [← kmswWindowVertexMapInf_eq_stage _ _ _ _ hv] at hm
    exact hm
  refine ⟨?_, ?_⟩
  · by_contra hsmall
    have hu : u = 0 ∨ u = 1 := by omega
    have ht : b ≤ (0 : ℤ) - M := by
      apply hb M 0
      rcases hu with hu | hu
      · left
        simpa only [kmswStage, kmswInit, ← hu] using hι
      · right
        simpa only [kmswStage, kmswInit, ← hu] using hι
    omega
  · intro k hk
    have hιk : wholePlaneVertexι W M (kmswStage (shiftedStream W M) k).nextVertex =
        wholePlaneVertexι W N v := by rw [← hk]; exact hι
    have hku : k < M - N + J := by
      by_contra hnot
      have hm := CutConverse.nextVertex_mono (shiftedStream W M)
        (show M - N + J ≤ k by omega)
      change u = _ at hk
      omega
    have escape (ht : b ≤ ((k + 1 : ℕ) : ℤ) - M) :
        minR (shiftedStream W M) k < R (shiftedStream W M) k := by
      have hmem : (k : ℤ) - M ∈ s := by
        apply Finset.mem_Icc.mpr
        have hMN : M - N + N = M := Nat.sub_add_cancel hNM
        constructor <;> omega
      have hle : f ((k : ℤ) - M) ≤ M := (Finset.le_sup hmem).trans hsup
      have htB := Classical.choose_spec (hB ((k : ℤ) - M)) M hle
      have hind : ((k : ℤ) - M + (M : ℤ)).toNat = k := by omega
      simpa only [hind] using htB.2
    intro hdown hUR
    have hrec := (kmswStage_UR_eq_nil_iff_record _ k).mp hUR
    have he : (kmswStage (shiftedStream W M) (k + 1)).east
        (act (shiftedStream W M) (k + 1)) =
        (kmswStage (shiftedStream W M) k).nextVertex := by
      simp [act, kmswStage, kmswStep, hdown, kmswStepOfStep, hUR, State.addEdge]
    have ht := hb M (k + 1) (Or.inr (by rw [he]; exact hιk))
    exact (ne_of_lt (escape ht)) hrec.symm

private theorem run_eventually_not_frontier (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w)
    (hL : ∀ a : ℤ, ∃ n, L w n ≤ a) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (v : ℕ) : ∃ Q, ∀ n ≥ Q, ¬ UpperFrontierEndpoint (kmswStage w n) v := by
  classical
  let I := {e : ℕ | edgeWest w e = v ∨ edgeEast w e = v}
  have hI : I.Finite := (hfin v).subset (by
    intro e he
    have hb := kmsw_edge_allocated_by_self w e
    have hs := edge_endpoints_eq w hb
    refine ⟨e, hb, ?_⟩
    simpa only [hs.1, hs.2] using
      (show edgeWest w e = v ∨ edgeEast w e = v from he))
  obtain ⟨B, hB⟩ := hI.bddAbove
  have ht := hI.preimage (CutConverse.act_injective w).injOn
  obtain ⟨T, hT⟩ := ht.bddAbove
  obtain ⟨qL, hqL⟩ := hL (minL w T - 1)
  obtain ⟨qR, hqR⟩ := hR (minR w (B + 1) - 1)
  have hTL : T < qL := by
    by_contra h
    have hm := runningMin_le (L w) T qL (by omega)
    change minL w T ≤ L w qL at hm
    omega
  have hBR : B + 1 < qR := by
    by_contra h
    have hm := runningMin_le (R w) (B + 1) qR (by omega)
    change minR w (B + 1) ≤ R w qR at hm
    omega
  obtain ⟨J, hJ⟩ := kmsw_vertex_allocated_of_finite_incidence w hfin v
  refine ⟨max J (max qL qR), ?_⟩
  intro n hn hf
  have hv : v < (kmswStage w n).nextVertex :=
    hJ.trans_le (CutConverse.nextVertex_mono w (by omega))
  rcases hf with ⟨e, he, hend⟩ | hf
  · have heid := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at he ⊢
      tauto)
    have hs := edge_endpoints_eq w heid
    have hi : e ∈ I := by
      change edgeWest w e = v ∨ edgeEast w e = v
      simpa only [hs.1, hs.2] using hend
    rcases List.mem_append.mp he with he | he
    · rw [kmswStage_UL_eq] at he
      obtain ⟨k, hk, hke⟩ := List.mem_map.mp he
      have hrec := of_decide_eq_true (List.mem_filter.mp hk).2
      have hkT : k ≤ T := hT (by change act w k ∈ I; rw [hke]; exact hi)
      have hlow := runningMin_le (L w) T k hkT
      change minL w T ≤ L w k at hlow
      have hhigh := hrec qL (by omega) (by omega)
      omega
    · rw [kmswStage_UR_eq] at he
      obtain ⟨k, hk, hke⟩ := List.mem_map.mp he
      have hrec := of_decide_eq_true (List.mem_filter.mp (List.mem_reverse.mp hk)).2
      have hek : k ≤ e := by
        have hb := kmsw_edge_allocated_by_self w k
        change (kmswStage w k).nextEdge - 1 = e at hke
        omega
      have heB : e ≤ B := hB hi
      have hlow := runningMin_le (R w) (B + 1) (k - 1) (by omega)
      change minR w (B + 1) ≤ R w (k - 1) at hlow
      have hhigh := hrec.2.2 qR (by omega) (by omega)
      omega
  · omega

private theorem stage_path_into_colimit (W : ℤ → Fin 3) (N n : ℕ)
    {c k v : ℕ}
    (hp : KMSWStagePath (fun _ _ => True) (kmswStage (shiftedStream W N) n)
      Set.univ c k v) :
    WholePlanePath W Set.univ (wholePlaneVertexι W N c) k
      (wholePlaneVertexι W N v) := by
  induction hp with
  | nil _ => exact .nil (Set.mem_univ _)
  | snoc hp _ _ ha ih =>
    obtain ⟨⟨e, b⟩, _, hx, hy⟩ := ha
    have hs := edge_endpoints_eq (shiftedStream W N) e.isLt
    apply WholePlanePath.snoc ih (Set.mem_univ _) (Set.mem_univ _)
    refine ⟨wholePlaneEdgeι W N e.val, ?_⟩
    rw [wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι]
    cases b
    · exact Or.inl ⟨congrArg _ (hs.1.symm.trans hx),
        congrArg _ (hs.2.symm.trans hy)⟩
    · exact Or.inr ⟨congrArg _ (hs.1.symm.trans hy),
        congrArg _ (hs.2.symm.trans hx)⟩

private theorem event_frontier_transport (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex)
    (hfresh : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hfront : ¬ UpperFrontierEndpoint (kmswStage (fun i => w (s + i)) m) v) :
    ¬ UpperFrontierEndpoint (kmswStage w (s + m))
      (kmswWindowPatchVertexMap w s m v) := by
  let F := kmswStage (fun i => w (s + i)) m
  let G := kmswStage w (s + m)
  let G₀ := kmswStage w s
  let d := kmswWindowPatchData w s m
  let ψ := kmswWindowPatchVertexMap w s m
  have hrel := kmswWindowPatchData_rel w s m
  have hvr := kmswWindowPatchVertexMap_rel w s m
  change KMSWWindowPatchRel G₀ G F d.φ d.A d.B d.YL d.YR d.XL d.XR at hrel
  change KMSWWindowPatchVertexRel G F d.φ ψ at hvr
  have hres (e : ℕ) (he : e ∈ d.A ++ d.B) :
      G.west e < G₀.nextVertex ∧ G.east e < G₀.nextVertex := by
    have hbase : e ∈ G₀.UL ++ G₀.UR := by
      rcases List.mem_append.mp he with ha | hb
      · apply List.mem_append_left
        apply List.dropLast_subset
        rw [hrel.left_residual]
        exact List.mem_append_left _ ha
      · apply List.mem_append_right
        rw [hrel.right_residual]
        exact List.mem_append_right _ hb
    have heid := (kmswStage_boundary_ids_lt_nextEdge w s).2 e (by
      change e ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR
      simp only [List.mem_append] at hbase ⊢
      tauto)
    have hs := kmswStage_endpoints_stable w (show s ≤ s + m by omega) heid
    change G.west e = G₀.west e ∧ G.east e = G₀.east e at hs
    rw [hs.1, hs.2]
    exact kmswStage_endpoints_lt_nextVertex w s e heid
  rintro (⟨e, he, hend⟩ | hnew)
  · change e ∈ G.UL ++ G.UR at he
    have hsplit : e ∈ d.A ++ d.B ∨
        ∃ f, f ∈ F.UL ++ F.UR ∧ d.φ f = e := by
      rw [hrel.ul, hrel.ur] at he
      simp only [List.mem_append] at he
      rcases he with (ha | hul) | (hur | hb)
      · exact Or.inl (List.mem_append_left _ ha)
      · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hul
        exact Or.inr ⟨f, List.mem_append_left _ hf, hfe⟩
      · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hur
        exact Or.inr ⟨f, List.mem_append_right _ hf, hfe⟩
      · exact Or.inl (List.mem_append_right _ hb)
    rcases hsplit with hresid | ⟨f, hf, rfl⟩
    · have hb := hres e hresid
      change G.west e = ψ v ∨ G.east e = ψ v at hend
      change G₀.nextVertex ≤ ψ v at hfresh
      rcases hend with hw | he
      · omega
      · omega
    · have hfid := (kmswStage_boundary_ids_lt_nextEdge
          (fun i => w (s + i)) m).2 f (by
        change f ∈ F.UL ++ F.UR ++ F.LL ++ F.LR
        simp only [List.mem_append] at hf ⊢
        tauto)
      have hb := kmswStage_endpoints_lt_nextVertex (fun i => w (s + i)) m f hfid
      change G.west (d.φ f) = ψ v ∨ G.east (d.φ f) = ψ v at hend
      apply hfront
      left
      refine ⟨f, hf, ?_⟩
      rcases hend with hw | he
      · left
        exact kmswWindowPatchVertexMap_injOn w s m hb.1 hv
          ((hvr.west_endpoint f hfid).trans hw)
      · right
        exact kmswWindowPatchVertexMap_injOn w s m hb.2 hv
          ((hvr.east_endpoint f hfid).trans he)
  · exact (Nat.not_le_of_gt (hvr.vertex_bound v hv)) hnew

private theorem vertex_eventually_not_frontier (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hforward : ∀ M, (∀ a : ℤ, ∃ n, L (shiftedStream W M) n ≤ a) ∧
      (∀ a : ℤ, ∃ n, R (shiftedStream W M) n ≤ a)) (N v : ℕ) :
    ∃ A, ∃ hNA : N ≤ A, ∀ M (hAM : A ≤ M),
      let z := wholePlaneVertexTrans W N M (hNA.trans hAM) v
      z < (kmswStage (shiftedStream W M) (2 * M)).nextVertex ∧
        ¬ UpperFrontierEndpoint (kmswStage (shiftedStream W M) (2 * M)) z := by
  obtain ⟨P, hNP, hP⟩ := H.2 N v
  let a := wholePlaneVertexTrans W N P hNP v
  obtain ⟨J, hJ⟩ := kmsw_vertex_allocated_of_finite_incidence
    (shiftedStream W P) (H.1 P) a
  obtain ⟨Q, hQ⟩ := run_eventually_not_frontier (shiftedStream W P)
    (H.1 P) (hforward P).1 (hforward P).2 a
  let A := max P (max J Q)
  have hPA : P ≤ A := Nat.le_max_left _ _
  refine ⟨A, hNP.trans hPA, ?_⟩
  intro M hAM
  have hPM : P ≤ M := hPA.trans hAM
  let m := M + P
  have ham : a < (kmswStage (shiftedStream W P) m).nextVertex :=
    hJ.trans_le (CutConverse.nextVertex_mono _ (by dsimp [A] at hAM; omega))
  have ham' : a <
      (kmswStage (fun i => shiftedStream W M ((M - P) + i)) m).nextVertex := by
    rw [shiftedStream_shift W P M hPM]
    exact ham
  have hmap : kmswWindowPatchVertexMap (shiftedStream W M) (M - P) m a =
      wholePlaneVertexTrans W N M ((hNP.trans hPA).trans hAM) v := by
    rw [← kmswWindowVertexMapInf_eq_stage _ _ _ _ ham']
    exact congrFun (wholePlaneVertexTrans_comp W N P M hNP hPM) v
  have hend : M - P + m = 2 * M := by dsimp [m]; omega
  have hbound := (kmswWindowPatchVertexMap_rel (shiftedStream W M) (M - P) m).vertex_bound
    a ham'
  rw [hmap, hend] at hbound
  refine ⟨hbound, ?_⟩
  have hfresh : (kmswStage (shiftedStream W M) (M - P)).nextVertex ≤
      kmswWindowPatchVertexMap (shiftedStream W M) (M - P) m a := by
    rw [← kmswWindowVertexMapInf_eq_stage _ _ _ _ ham']
    exact hP M hPM
  have hf := event_frontier_transport (shiftedStream W M) (M - P) m a ham' hfresh
    (by rw [shiftedStream_shift W P M hPM]; exact hQ m (by dsimp [A, m] at *; omega))
  rw [hmap, hend] at hf
  exact hf

private theorem cast_list (xs : List ℕ) :
    (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl

private theorem range_fst (f : ℕ → ℤ × ℤ) (n : ℕ) :
    ((List.range n).map f).sum.1 =
      ∑ i ∈ Finset.range n, (f i).1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem window_integral_fst (W : ℤ → Fin 3) (N j : ℕ) :
    L (shiftedStream W N) N +
      (wholePlaneWordIntegral W ((j : ℤ) - N)).1 =
      L (shiftedStream W N) j := by
  by_cases hj : j < N
  · have hd : ((j : ℤ) - N) < 0 := by omega
    have hc : (-((j : ℤ) - N)).toNat = N - j := by omega
    simp only [wholePlaneWordIntegral, ite_eq_right (not_le.mpr hd), Prod.fst_neg,
      hc, bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_fst]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).1) j (N - j)
    have ht : (∑ i ∈ Finset.range (N - j),
        (lazyTwoDimensionalStep (shiftedStream W N (j + i))).1) =
        ∑ i ∈ Finset.range (N - j),
          (lazyTwoDimensionalStep (W (-(i : ℤ) - 1))).1 := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show j + (N - j) = N by omega, ht] at he
    change L (shiftedStream W N) N = L (shiftedStream W N) j + _ at he
    omega
  · have hd : 0 ≤ (j : ℤ) - N := by omega
    have hc : ((j : ℤ) - N).toNat = j - N := by omega
    simp only [wholePlaneWordIntegral, ite_eq_left hd, hc,
      bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_fst]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).1) N (j - N)
    have ht : (∑ i ∈ Finset.range (j - N),
        (lazyTwoDimensionalStep (shiftedStream W N (N + i))).1) =
        ∑ i ∈ Finset.range (j - N), (lazyTwoDimensionalStep (W (i : ℤ))).1 := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show N + (j - N) = j by omega, ht] at he
    exact he.symm

private theorem range_snd (f : ℕ → ℤ × ℤ) (n : ℕ) :
    ((List.range n).map f).sum.2 =
      ∑ i ∈ Finset.range n, (f i).2 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem window_integral_snd (W : ℤ → Fin 3) (N j : ℕ) :
    R (shiftedStream W N) N +
      (wholePlaneWordIntegral W ((j : ℤ) - N)).2 =
      R (shiftedStream W N) j := by
  by_cases hj : j < N
  · have hd : ((j : ℤ) - N) < 0 := by omega
    have hc : (-((j : ℤ) - N)).toNat = N - j := by omega
    simp only [wholePlaneWordIntegral, ite_eq_right (not_le.mpr hd), Prod.snd_neg,
      hc, bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_snd]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).2) j (N - j)
    have ht : (∑ i ∈ Finset.range (N - j),
        (lazyTwoDimensionalStep (shiftedStream W N (j + i))).2) =
        ∑ i ∈ Finset.range (N - j),
          (lazyTwoDimensionalStep (W (-(i : ℤ) - 1))).2 := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show j + (N - j) = N by omega, ht] at he
    change R (shiftedStream W N) N = R (shiftedStream W N) j + _ at he
    omega
  · have hd : 0 ≤ (j : ℤ) - N := by omega
    have hc : ((j : ℤ) - N).toNat = j - N := by omega
    simp only [wholePlaneWordIntegral, ite_eq_left hd, hc,
      bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_snd]
    have he := Finset.sum_range_add
      (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).2) N (j - N)
    have ht : (∑ i ∈ Finset.range (j - N),
        (lazyTwoDimensionalStep (shiftedStream W N (N + i))).2) =
        ∑ i ∈ Finset.range (j - N), (lazyTwoDimensionalStep (W (i : ℤ))).2 := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      unfold shiftedStream
      congr 1
      omega
    rw [show N + (j - N) = j by omega, ht] at he
    exact he.symm

private theorem initial_trans (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    wholePlaneVertexTrans W N M h (activeInitial (shiftedStream W N) k) =
      activeInitial (shiftedStream W M) (M - N + k) := by
  have he : wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
    simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
      windowEdgeMapInf_act (shiftedStream W M) (M - N) k
  unfold activeInitial
  rw [← wholePlaneEdgeTrans_west, he]

private theorem run_R_unbounded (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a) (N : ℕ) :
    ∀ a : ℤ, ∃ n, R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) n ≤ a := by
  intro a
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨n, hn⟩ := hP1 (a - R (shiftedStream W N) N)
  refine ⟨N + n, ?_⟩
  have he := window_integral_snd W N (N + n)
  have ha : ((N + n : ℕ) : ℤ) - N = (n : ℤ) := by omega
  rw [ha, wholePlaneWordIntegral_uibhbotCodeWord] at he
  change R (shiftedStream W N) (N + n) ≤ a
  omega

private theorem run_coordinates_unbounded (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a) (N : ℕ) :
    (∀ a : ℤ, ∃ n, L (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) n ≤ a) ∧
    (∀ a : ℤ, ∃ n, R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) n ≤ a) := by
  refine ⟨?_, run_R_unbounded w hw hP1 N⟩
  intro a
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨n, hn⟩ := uibhbotConcatWalk_fst_unbounded_below_of_stopped w hw
    (a - L (shiftedStream W N) N)
  refine ⟨N + n, ?_⟩
  have he := window_integral_fst W N (N + n)
  have ha : ((N + n : ℕ) : ℤ) - N = (n : ℤ) := by omega
  rw [ha, wholePlaneWordIntegral_uibhbotCodeWord] at he
  change L (shiftedStream W N) (N + n) ≤ a
  omega

private theorem relaxed_capture_eventually (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k))
    (hforward : ∀ M, (∀ a : ℤ, ∃ n, L (shiftedStream W M) n ≤ a) ∧
      (∀ a : ℤ, ∃ n, R (shiftedStream W M) n ≤ a)) (N0 c0 r : ℕ) :
    ∃ N1, ∃ h0 : N0 ≤ N1, ∀ N (hN : N1 ≤ N),
      kmswWindowCaptureEventStrongRel (shiftedStream W N) (2 * N) r
        (wholePlaneVertexTrans W N0 N (h0.trans hN) c0) := by
  classical
  let x := wholePlaneVertexι W N0 c0
  let B := wholePlaneBallVertices W r x
  have hBfin := wholePlaneBallVertices_finite W H r x
  have hx (y : WholePlaneVertex W) : ∃ A, ∀ N ≥ A, ∃ v,
      wholePlaneVertexι W N v = y ∧
      v < (kmswStage (shiftedStream W N) (2 * N)).nextVertex ∧
      (2 ≤ v ∧ ∀ k, v = (kmswStage (shiftedStream W N) k).nextVertex →
        kmswCodeStep (shiftedStream W N k) = .down →
          (kmswStage (shiftedStream W N) k).UR ≠ []) ∧
      ¬ UpperFrontierEndpoint (kmswStage (shiftedStream W N) (2 * N)) v := by
    obtain ⟨⟨P, a⟩, rfl⟩ := Quotient.exists_rep y
    obtain ⟨A, hPA, hA⟩ := vertex_eventually_not_frontier W H hforward P a
    obtain ⟨D, hPD, hD⟩ := vertex_eventually_down_nonrecord W H hB P a
    refine ⟨max A D, ?_⟩
    intro N hAN
    have hA' : A ≤ N := (Nat.le_max_left _ _).trans hAN
    have hD' : D ≤ N := (Nat.le_max_right _ _).trans hAN
    exact ⟨wholePlaneVertexTrans W P N (hPA.trans hA') a,
      congrFun (wholePlaneVertexι_trans W P N (hPA.trans hA')) a,
      (hA N hA').1, hD N hD', (hA N hA').2⟩
  choose f hf using hx
  let N1 := max N0 (hBfin.toFinset.sup f)
  have h0 : N0 ≤ N1 := Nat.le_max_left _ _
  refine ⟨N1, h0, ?_⟩
  intro N hN
  let c := wholePlaneVertexTrans W N0 N (h0.trans hN) c0
  have hc : wholePlaneVertexι W N c = x :=
    congrFun (wholePlaneVertexι_trans W N0 N (h0.trans hN)) c0
  have hlarge {y : WholePlaneVertex W} (hy : y ∈ B) : f y ≤ N :=
    (Finset.le_sup (hBfin.mem_toFinset.mpr hy)).trans
      ((Nat.le_max_right _ _).trans hN)
  have hcenter : x ∈ B := ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
  obtain ⟨v, hv, hval⟩ := hf x N (hlarge hcenter)
  have hvc : v = c := wholePlaneVertexι_injective W N (hv.trans hc.symm)
  have hcb : c < (kmswStage (shiftedStream W N) (2 * N)).nextVertex := hvc ▸ hval.1
  have hgood (v : ℕ)
      (hv : v ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage (shiftedStream W N) (2 * N)) r c) :
      (2 ≤ v ∧ ∀ k, v = (kmswStage (shiftedStream W N) k).nextVertex →
        kmswCodeStep (shiftedStream W N k) = .down →
          (kmswStage (shiftedStream W N) k).UR ≠ []) ∧
        ¬ UpperFrontierEndpoint (kmswStage (shiftedStream W N) (2 * N)) v := by
    obtain ⟨k, hk, hp⟩ := (Finset.mem_filter.mp hv).2
    have hball : wholePlaneVertexι W N v ∈ B := by
      have hp' := stage_path_into_colimit W N (2 * N) hp
      rw [hc] at hp'
      exact ⟨k, hk, hp'⟩
    obtain ⟨a, ha, hprop⟩ := hf (wholePlaneVertexι W N v) N (hlarge hball)
    have hav := wholePlaneVertexι_injective W N ha
    exact hav ▸ hprop.2
  refine ⟨⟨hcb, ?_, ?_⟩, ?_⟩
  · intro v hv
    have hn := (hgood v hv).1
    refine ⟨hn.1, ?_⟩
    intro k _ hk
    exact hn.2 k hk
  · intro v hv
    obtain ⟨hb, k, hk, hp⟩ := Finset.mem_filter.mp hv
    exact (hgood v (Finset.mem_filter.mpr ⟨hb, k, by omega, hp⟩)).2
  · intro v hv
    exact (hgood v hv).2

private theorem vertex_eventually_left_barrier (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (H : WholePlaneRotationHypothesis (uibhbotCodeWord w (fun k => (hw k).1)))
    (N v : ℕ) :
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    ∃ A, ∃ hNA : N ≤ A, ∀ M (hAM : A ≤ M), ∀ k,
      wholePlaneVertexTrans W N M (hNA.trans hAM) v =
        (kmswStage (shiftedStream W M) k).nextVertex →
      kmswCodeStep (shiftedStream W M k) = .left →
      (kmswStage (shiftedStream W M) k).UL.dropLast.reverse = [] →
      ∀ s : ℤ, s < -(M : ℤ) →
        (uibhbotConcatWalk w ((k : ℤ) - M)).1 ≤ (uibhbotConcatWalk w s).1 := by
  classical
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  obtain ⟨b, hb⟩ := incident_active_time_lower_bound W (wholePlaneVertexι W N v)
    (wholePlane_incidentEdges_finite W H (wholePlaneVertexι W N v))
  obtain ⟨J, hJ⟩ := kmsw_vertex_allocated_of_finite_incidence
    (shiftedStream W N) (H.1 N) v
  let S := Finset.Icc (b - 1) ((J : ℤ) - N)
  let f : ℤ → ℕ := fun t => (1 - Classical.choose (uibhbotConcatWalk_D2 w hw t)).toNat
  let A := max N (S.sup f)
  have hNA : N ≤ A := Nat.le_max_left _ _
  refine ⟨A, hNA, ?_⟩
  intro M hAM k hk hl hUL s hs
  change wholePlaneVertexTrans W N M (hNA.trans hAM) v =
    (kmswStage (shiftedStream W M) k).nextVertex at hk
  change kmswCodeStep (shiftedStream W M k) = .left at hl
  change (kmswStage (shiftedStream W M) k).UL.dropLast.reverse = [] at hUL
  have hNM : N ≤ M := hNA.trans hAM
  let u := wholePlaneVertexTrans W N M hNM v
  have hι : wholePlaneVertexι W M u = wholePlaneVertexι W N v :=
    congrFun (wholePlaneVertexι_trans W N M hNM) v
  have huBound : u < (kmswStage (shiftedStream W M) (M - N + J)).nextVertex := by
    have hv : v < (kmswStage (fun i => shiftedStream W M (M - N + i)) J).nextVertex := by
      rw [shiftedStream_shift W N M hNM]
      exact hJ
    have hm := (kmswWindowPatchVertexMap_rel (shiftedStream W M) (M - N) J).vertex_bound
      v hv
    rw [← kmswWindowVertexMapInf_eq_stage _ _ _ _ hv] at hm
    exact hm
  have hku : k < M - N + J := by
    by_contra hnot
    have hm := CutConverse.nextVertex_mono (shiftedStream W M)
      (show M - N + J ≤ k by omega)
    change u = _ at hk
    omega
  have he : (kmswStage (shiftedStream W M) (k + 1)).west
      (act (shiftedStream W M) (k + 1)) =
      (kmswStage (shiftedStream W M) k).nextVertex := by
    simp [act, kmswStage, kmswStep, hl, kmswStepOfStep, hUL, State.addEdge]
  have hιk : wholePlaneVertexι W M (kmswStage (shiftedStream W M) k).nextVertex =
      wholePlaneVertexι W N v := by rw [← hk]; exact hι
  have ht := hb M (k + 1) (Or.inl (by rw [he]; exact hιk))
  have hmem : (k : ℤ) - M ∈ S := by
    apply Finset.mem_Icc.mpr
    have hMN : M - N + N = M := Nat.sub_add_cancel hNM
    constructor <;> omega
  have hlarge : f ((k : ℤ) - M) ≤ M :=
    (Finset.le_sup hmem).trans ((Nat.le_max_right _ _).trans hAM)
  have hstart : s < Classical.choose (uibhbotConcatWalk_D2 w hw ((k : ℤ) - M)) := by
    dsimp only [f] at hlarge
    omega
  exact (Classical.choose_spec (uibhbotConcatWalk_D2 w hw ((k : ℤ) - M)) s hstart).le





theorem uibhbotCodeWord_eventualRelaxedCapture (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a)
    (hP2 : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
         R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k)) (r : ℕ) :
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    ∃ N₀, ∀ N ≥ N₀,
      let c := activeInitial (shiftedStream W N) N
      kmswWindowCaptureEventStrongRel (shiftedStream W N) (2 * N) r c ∧
        ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r c,
          minL (shiftedStream W N) k = L (shiftedStream W N) k := by
  classical
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  have H := uibhbotCodeWord_rotationHypothesis w hw hP1 hP2
  obtain ⟨N₀, h0, hN₀⟩ := relaxed_capture_eventually W H hP2
    (run_coordinates_unbounded w hw hP1) 0 (activeInitial (shiftedStream W 0) 0) r
  refine ⟨N₀, ?_⟩
  intro N hN
  have hev := hN₀ N hN
  rw [initial_trans] at hev
  simp only [Nat.sub_zero, Nat.add_zero] at hev
  refine ⟨hev, ?_⟩
  intro k hk
  have hs := (Finset.mem_filter.mp hk).2.2.2
  exact ((kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ k).mp hs).symm





theorem uibhbotCodeWord_eventualLeftSeamBarrier (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hP1 : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a)
    (hP2 : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k <
         R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) k)) (r : ℕ) :
    let W := uibhbotCodeWord w (fun k => (hw k).1)
    ∃ N₀, ∀ N ≥ N₀,
      let c := activeInitial (shiftedStream W N) N
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) (2 * N) r c,
        ∀ s : ℤ, s < -(N : ℤ) →
          (uibhbotConcatWalk w ((k : ℤ) - N)).1 ≤ (uibhbotConcatWalk w s).1 := by
  classical
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  have H := uibhbotCodeWord_rotationHypothesis w hw hP1 hP2
  let x := wholePlaneVertexι W 0 (activeInitial (shiftedStream W 0) 0)
  let B := wholePlaneBallVertices W r x
  have hBfin := wholePlaneBallVertices_finite W H r x
  have hx (y : WholePlaneVertex W) : ∃ A, ∀ N ≥ A, ∃ v,
      wholePlaneVertexι W N v = y ∧
        ∀ k, v = (kmswStage (shiftedStream W N) k).nextVertex →
          kmswCodeStep (shiftedStream W N k) = .left →
          (kmswStage (shiftedStream W N) k).UL.dropLast.reverse = [] →
          ∀ s : ℤ, s < -(N : ℤ) →
            (uibhbotConcatWalk w ((k : ℤ) - N)).1 ≤ (uibhbotConcatWalk w s).1 := by
    obtain ⟨⟨P, a⟩, rfl⟩ := Quotient.exists_rep y
    obtain ⟨A, hPA, hA⟩ := vertex_eventually_left_barrier w hw H P a
    refine ⟨A, ?_⟩
    intro N hAN
    exact ⟨wholePlaneVertexTrans W P N (hPA.trans hAN) a,
      congrFun (wholePlaneVertexι_trans W P N (hPA.trans hAN)) a, hA N hAN⟩
  choose f hf using hx
  refine ⟨hBfin.toFinset.sup f, ?_⟩
  intro N hN
  dsimp only
  intro k hk
  obtain ⟨⟨v, hv, hcreate⟩, hl, hUL⟩ := (Finset.mem_filter.mp hk).2
  have hc : wholePlaneVertexι W N (activeInitial (shiftedStream W N) N) = x := by
    have ht := congrFun (wholePlaneVertexι_trans W 0 N (Nat.zero_le N))
      (activeInitial (shiftedStream W 0) 0)
    simp only [Function.comp_apply] at ht
    rw [initial_trans] at ht
    simpa only [Nat.sub_zero, Nat.add_zero] using ht
  obtain ⟨j, hj, hp⟩ := (Finset.mem_filter.mp hv).2
  have hball : wholePlaneVertexι W N v ∈ B := by
    have hp' := stage_path_into_colimit W N (2 * N) hp
    rw [hc] at hp'
    exact ⟨j, hj, hp'⟩
  have hlarge : f (wholePlaneVertexι W N v) ≤ N :=
    (Finset.le_sup (hBfin.mem_toFinset.mpr hball)).trans hN
  obtain ⟨a, ha, hprop⟩ := hf (wholePlaneVertexι W N v) N hlarge
  have hav : a = v := wholePlaneVertexι_injective W N ha
  exact hprop k (hav.trans hcreate) hl hUL

end DirectedDistances.KMSW
