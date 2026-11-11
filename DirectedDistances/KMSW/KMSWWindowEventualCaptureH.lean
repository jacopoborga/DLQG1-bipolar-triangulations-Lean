module

public import DirectedDistances.KMSW.KMSWWindowEventualCapture
public import DirectedDistances.KMSW.WholePlaneRotationAE

import DirectedDistances.KMSW.WholePlaneCrossRunRotation

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.KMSW
open MeasureTheory

private theorem incident_lifts_of_fresh (W : ℤ → Fin 3) (N M : ℕ)
    (hNM : N ≤ M) (v e : ℕ) (hf : wholePlaneFresh W N M hNM v)
    (he : edgeWest (shiftedStream W M) e = wholePlaneVertexTrans W N M hNM v ∨
      edgeEast (shiftedStream W M) e = wholePlaneVertexTrans W N M hNM v) :
    ∃ f, wholePlaneEdgeTrans W N M hNM f = e ∧
      (edgeWest (shiftedStream W N) f = v ∨ edgeEast (shiftedStream W N) f = v) := by
  classical
  have lift (b : Bool)
      (hb : (if b then edgeEast (shiftedStream W M) e
        else edgeWest (shiftedStream W M) e) = wholePlaneVertexTrans W N M hNM v) :
      ∃ d, wholePlaneDartTrans W N M hNM d = (e, b) := by
    by_contra h
    exact (wholePlaneDartTrans_not_mem_range_not_fresh W N M hNM v (e, b) h hb) hf
  rcases he with hw | he
  · obtain ⟨d, hd⟩ := lift false hw
    have heq := congrArg Prod.fst hd
    have hside := congrArg Prod.snd hd
    change wholePlaneEdgeTrans W N M hNM d.1 = e at heq
    change d.2 = false at hside
    refine ⟨d.1, heq, Or.inl ?_⟩
    apply wholePlaneVertexTrans_injective W N M hNM
    rw [← wholePlaneEdgeTrans_west, heq, hw]
  · obtain ⟨d, hd⟩ := lift true he
    have heq := congrArg Prod.fst hd
    change wholePlaneEdgeTrans W N M hNM d.1 = e at heq
    refine ⟨d.1, heq, Or.inr ?_⟩
    apply wholePlaneVertexTrans_injective W N M hNM
    rw [← wholePlaneEdgeTrans_east, heq, he]




theorem wholePlane_incidentEdges_finite (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (x : WholePlaneVertex W) :
    {e : WholePlaneEdge W |
      wholePlaneEdgeWest W e = x ∨ wholePlaneEdgeEast W e = x}.Finite := by
  classical
  obtain ⟨⟨N, v⟩, rfl⟩ := Quotient.exists_rep x
  obtain ⟨M, hNM, hf⟩ := H.2 N v
  let a := wholePlaneVertexTrans W N M hNM v
  let S := {e : ℕ | ∃ n, e < (kmswStage (shiftedStream W M) n).nextEdge ∧
    ((kmswStage (shiftedStream W M) n).west e = a ∨
      (kmswStage (shiftedStream W M) n).east e = a)}
  apply ((H.1 M a).image (wholePlaneEdgeι W M)).subset
  intro e he
  obtain ⟨⟨L, q⟩, rfl⟩ := Quotient.exists_rep e
  let K := max M L
  have hMK : M ≤ K := Nat.le_max_left _ _
  have hLK : L ≤ K := Nat.le_max_right _ _
  let f := wholePlaneEdgeTrans W L K hLK q
  have hx : wholePlaneVertexι W K (wholePlaneVertexTrans W M K hMK a) =
      wholePlaneVertexι W N v :=
    (congrFun (wholePlaneVertexι_trans W M K hMK) a).trans
      (congrFun (wholePlaneVertexι_trans W N M hNM) v)
  have hw : wholePlaneVertexι W K (edgeWest (shiftedStream W K) f) =
      wholePlaneEdgeWest W (wholePlaneEdgeι W L q) := by
    rw [wholePlaneEdgeWest_ι, wholePlaneEdgeTrans_west]
    exact congrFun (wholePlaneVertexι_trans W L K hLK) _
  have ha : wholePlaneVertexι W K (edgeEast (shiftedStream W K) f) =
      wholePlaneEdgeEast W (wholePlaneEdgeι W L q) := by
    rw [wholePlaneEdgeEast_ι, wholePlaneEdgeTrans_east]
    exact congrFun (wholePlaneVertexι_trans W L K hLK) _
  have hinc : edgeWest (shiftedStream W K) f = wholePlaneVertexTrans W M K hMK a ∨
      edgeEast (shiftedStream W K) f = wholePlaneVertexTrans W M K hMK a := by
    rcases he with he | he
    · exact Or.inl (wholePlaneVertexι_injective W K ((hw.trans he).trans hx.symm))
    · exact Or.inr (wholePlaneVertexι_injective W K ((ha.trans he).trans hx.symm))
  obtain ⟨g, hg, hga⟩ := incident_lifts_of_fresh W M K hMK a f (hf K hMK) hinc
  have hge := kmsw_edge_allocated_by_self (shiftedStream W M) g
  have hends := edge_endpoints_eq (shiftedStream W M) hge
  refine ⟨g, ⟨g, hge, ?_⟩, ?_⟩
  · simpa only [hends.1, hends.2] using hga
  · exact (congrFun (wholePlaneEdgeι_trans W M K hMK) g).symm.trans
      ((congrArg (wholePlaneEdgeι W K) hg).trans
        (congrFun (wholePlaneEdgeι_trans W L K hLK) q))

private theorem neighbors_finite (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (x : WholePlaneVertex W) :
    {y | wholePlaneAdjacent W x y}.Finite := by
  let S := {e : WholePlaneEdge W |
    wholePlaneEdgeWest W e = x ∨ wholePlaneEdgeEast W e = x}
  have hs := wholePlane_incidentEdges_finite W H x
  apply ((hs.image (wholePlaneEdgeWest W)).union
    (hs.image (wholePlaneEdgeEast W))).subset
  rintro y ⟨e, he | he⟩
  · exact Or.inr ⟨e, Or.inl he.1, he.2⟩
  · exact Or.inl ⟨e, Or.inr he.2, he.1⟩




theorem wholePlaneBallVertices_finite (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (r : ℕ) (x : WholePlaneVertex W) :
    (wholePlaneBallVertices W r x).Finite := by
  induction r with
  | zero =>
    apply (Set.finite_singleton x).subset
    rintro y ⟨k, hk, hp⟩
    have hk0 : k = 0 := by omega
    subst k
    cases hp
    exact Set.mem_singleton x
  | succ r ih =>
    apply (ih.union (ih.biUnion (fun y _ => neighbors_finite W H y))).subset
    rintro z ⟨k, hk, hp⟩
    cases hp with
    | nil _ => exact Or.inl ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
    | @snoc n y z hp _ _ ha =>
      right
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨⟨n, by omega, hp⟩, ha⟩⟩

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





theorem wholePlaneVertex_eventually_nonrecord (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
       minL (shiftedStream W M) k < L (shiftedStream W M) k))
    (N v : ℕ) :
    ∃ A, ∃ hNA : N ≤ A, ∀ M (hAM : A ≤ M),
      KMSWNonrecordVertex (shiftedStream W M)
        (wholePlaneVertexTrans W N M (hNA.trans hAM) v) := by
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
        minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
        minL (shiftedStream W M) k < L (shiftedStream W M) k := by
      have hmem : (k : ℤ) - M ∈ s := by
        apply Finset.mem_Icc.mpr
        have hMN : M - N + N = M := Nat.sub_add_cancel hNM
        constructor <;> omega
      have hle : f ((k : ℤ) - M) ≤ M := (Finset.le_sup hmem).trans hsup
      have htB := Classical.choose_spec (hB ((k : ℤ) - M)) M hle
      have hind : ((k : ℤ) - M + (M : ℤ)).toNat = k := by omega
      simpa only [hind] using htB.2
    constructor
    · intro hdown hrec
      have hUR := (kmswStage_UR_eq_nil_iff_record _ k).mpr hrec
      have he : (kmswStage (shiftedStream W M) (k + 1)).east
          (act (shiftedStream W M) (k + 1)) =
          (kmswStage (shiftedStream W M) k).nextVertex := by
        simp [act, kmswStage, kmswStep, hdown, kmswStepOfStep, hUR, State.addEdge]
      have ht := hb M (k + 1) (Or.inr (by rw [he]; exact hιk))
      exact (ne_of_lt (escape ht).1) hrec.symm
    · intro hleft hrec
      have hUL := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ k).mpr hrec
      have he : (kmswStage (shiftedStream W M) (k + 1)).west
          (act (shiftedStream W M) (k + 1)) =
          (kmswStage (shiftedStream W M) k).nextVertex := by
        simp [act, kmswStage, kmswStep, hleft, kmswStepOfStep, hUL, State.addEdge]
      have ht := hb M (k + 1) (Or.inl (by rw [he]; exact hιk))
      exact (ne_of_lt (escape ht).2) hrec.symm

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






theorem wholePlaneVertex_eventually_not_upperFrontier (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
       minL (shiftedStream W M) k < L (shiftedStream W M) k))
    (hforward : ∀ M, (∀ a : ℤ, ∃ n, L (shiftedStream W M) n ≤ a) ∧
      (∀ a : ℤ, ∃ n, R (shiftedStream W M) n ≤ a)) (N v : ℕ) :
    ∃ A, ∃ hNA : N ≤ A, ∀ M (hAM : A ≤ M),
      let z := wholePlaneVertexTrans W N M (hNA.trans hAM) v
      z < (kmswStage (shiftedStream W M) (2 * M)).nextVertex ∧
        KMSWNonrecordVertex (shiftedStream W M) z ∧
        ¬ UpperFrontierEndpoint (kmswStage (shiftedStream W M) (2 * M)) z := by
  obtain ⟨P, hNP, hP⟩ := wholePlaneVertex_eventually_nonrecord W H hB N v
  let a := wholePlaneVertexTrans W N P hNP v
  have ha : KMSWNonrecordVertex (shiftedStream W P) a := by
    simpa only [wholePlaneVertexTrans_self, id_eq] using hP P le_rfl
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
  refine ⟨hbound, hP M hPM, ?_⟩
  have hnons : ∀ k < m, a = (kmswStage (shiftedStream W P) k).nextVertex →
      (kmswCodeStep (shiftedStream W P k) = .down →
        (kmswStage (shiftedStream W P) k).UR ≠ []) ∧
      (kmswCodeStep (shiftedStream W P k) = .left →
        (kmswStage (shiftedStream W P) k).UL.dropLast.reverse ≠ []) := by
    intro k _ hk
    exact ⟨fun hd he => (ha.2 k hk).1 hd
        ((kmswStage_UR_eq_nil_iff_record _ k).mp he),
      fun hl he => (ha.2 k hk).2 hl
        ((kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ k).mp he)⟩
  have hf := kmswWindowPatchVertexMap_not_upperFrontier_for_every_prefix
    (shiftedStream W P) m a ham ha.1 hnons
    (hQ m (by dsimp [A, m] at *; omega)) (shiftedStream W M) (M - P)
    (fun i _ => congrFun (shiftedStream_shift W P M hPM) i)
  rw [hmap, hend] at hf
  exact hf





theorem wholePlaneWindowCaptureEventStrong_eventually (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
       minL (shiftedStream W M) k < L (shiftedStream W M) k))
    (hforward : ∀ M, (∀ a : ℤ, ∃ n, L (shiftedStream W M) n ≤ a) ∧
      (∀ a : ℤ, ∃ n, R (shiftedStream W M) n ≤ a)) (N0 c0 r : ℕ) :
    ∃ N1, ∃ h0 : N0 ≤ N1, ∀ N (hN : N1 ≤ N),
      kmswWindowCaptureEventStrong (shiftedStream W N) (2 * N) r
        (wholePlaneVertexTrans W N0 N (h0.trans hN) c0) := by
  classical
  let x := wholePlaneVertexι W N0 c0
  let B := wholePlaneBallVertices W r x
  have hBfin := wholePlaneBallVertices_finite W H r x
  have hx (y : WholePlaneVertex W) : ∃ A, ∀ N ≥ A, ∃ v,
      wholePlaneVertexι W N v = y ∧
      v < (kmswStage (shiftedStream W N) (2 * N)).nextVertex ∧
      KMSWNonrecordVertex (shiftedStream W N) v ∧
      ¬ UpperFrontierEndpoint (kmswStage (shiftedStream W N) (2 * N)) v := by
    obtain ⟨⟨P, a⟩, rfl⟩ := Quotient.exists_rep y
    obtain ⟨A, hPA, hA⟩ := wholePlaneVertex_eventually_not_upperFrontier
      W H hB hforward P a
    refine ⟨A, ?_⟩
    intro N hAN
    exact ⟨wholePlaneVertexTrans W P N (hPA.trans hAN) a,
      congrFun (wholePlaneVertexι_trans W P N (hPA.trans hAN)) a, hA N hAN⟩
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
      KMSWNonrecordVertex (shiftedStream W N) v ∧
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
    exact ⟨fun hd he => (hn.2 k hk).1 hd
        ((kmswStage_UR_eq_nil_iff_record _ k).mp he),
      fun hl he => (hn.2 k hk).2 hl
        ((kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ k).mp he)⟩
  · intro v hv
    obtain ⟨hb, k, hk, hp⟩ := Finset.mem_filter.mp hv
    exact (hgood v (Finset.mem_filter.mpr ⟨hb, k, by omega, hp⟩)).2
  · intro v hv
    exact (hgood v hv).2

private theorem ae_run_coordinates_unbounded :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      (∀ a : ℤ, ∃ n, L (shiftedStream W N) n ≤ a) ∧
      (∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a) := by
  apply MeasureTheory.ae_all_iff.2
  intro N
  have hf : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      (∀ a : ℤ, ∃ n, (RandomWalk.codeWalk ω n).1 ≤ a) ∧
      (∀ a : ℤ, ∃ n, (RandomWalk.codeWalk ω n).2 ≤ a) := by
    filter_upwards [RandomWalk.ae_codeWalk_fst_unbounded_below,
      RandomWalk.ae_codeWalk_snd_unbounded_below] with ω hL hR using ⟨hL, hR⟩
  rw [← RandomWalk.wholePlaneIIDCodeMeasure_map_shiftedPath N] at hf
  have hp := MeasureTheory.ae_of_ae_map
    (RandomWalk.measurable_shiftedCodePath N).aemeasurable hf
  simpa [RandomWalk.codeWalk, RandomWalk.shiftedCodePath, L, R,
    Prod.fst_sum, Prod.snd_sum] using hp





theorem wholePlaneIID_ae_eventual_windowCaptureStrong :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure, ∀ N0 c0 r : ℕ,
      ∃ N1, ∃ h0 : N0 ≤ N1, ∀ N (hN : N1 ≤ N),
        kmswWindowCaptureEventStrong (shiftedStream W N) (2 * N) r
          (wholePlaneVertexTrans W N0 N (h0.trans hN) c0) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis,
    wholePlaneIID_ae_fixed_time_nonrecord, ae_run_coordinates_unbounded]
    with W H hB hforward N0 c0 r
  exact wholePlaneWindowCaptureEventStrong_eventually W H hB hforward N0 c0 r

end DirectedDistances.KMSW
