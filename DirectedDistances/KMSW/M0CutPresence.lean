module

public import DirectedDistances.KMSW.M0CutSeam
public import DirectedDistances.KMSW.M0CutLeftSide
public import DirectedDistances.KMSW.M0CutEdgeTransport
public import DirectedDistances.KMSW.WholePlaneRunRotationRestrict
public import DirectedDistances.KMSW.RunBoundaryStackSets
public import DirectedDistances.KMSW.KMSWFutureMapDistance

/-! Supporting lemmas for paper labels `thm-busemann` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW
open Quiver




@[expose] def m0CutMissing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (E : WholePlaneEdge W) : Prop :=
  (∃ P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)),
    ∃ j, P.edge j = E) ∨ ¬ wholePlaneEdgePresent W E




@[expose] def m0CutTail (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : WholePlaneDart W) : Prop :=
  wholePlaneDartTail W d ∧ ¬ m0CutMissing W H d.1




theorem m0Cut_not_present_iff_eventually_LL (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (e : ℕ) :
    ¬ EdgePresent w e ↔ ∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LL := by
  classical
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩
  constructor
  · intro hp
    obtain ⟨N, hN⟩ := kmswRun_UR_eventually_absent w hR e
    refine ⟨max N e, fun n hn => ?_⟩
    have he : e < (kmswStage w n).nextEdge :=
      (kmsw_edge_allocated_by_self w e).trans_le
        (kmswStage_nextEdge_mono w (by omega))
    have hfalse : (kmswStage w n).present e = false := by
      cases hb : (kmswStage w n).present e
      · rfl
      · exact (hp ⟨n, he, hb⟩).elim
    exact ((kmswStage_status w n).1 e he).mp hfalse |>.resolve_left
      (hN n (by omega))
  · rintro ⟨N, hN⟩ hp
    obtain ⟨M, hM⟩ := hp.eventually_present
    have hf := kmswStage_LL_edge_missing w (max N M) e (hN _ (le_max_left _ _))
    have ht := (hM (max N M) (le_max_right _ _)).2
    rw [hf] at ht
    cases ht




theorem m0Cut_missing_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) (a : ℕ) :
    m0CutMissing W H (wholePlaneEdgeι W 0 a) ↔
      ¬ EdgePresent (shiftedStream W 0) a := by
  constructor
  · rintro (⟨P, j, hj⟩ | hm)
    · have he := m0Cut_betaL_edges W H h hLL P j
      have ha := wholePlaneEdgeι_injective W 0 (he.symm.trans hj)
      rw [← ha]
      exact boundary_left_edge_not_present (shiftedStream W 0) h (by omega)
    · exact fun hp => hm (wholePlaneEdgePresent_ι_of_run_present W 0 a hp)
  · intro hm
    have he := (m0Cut_not_present_iff_eventually_LL (shiftedStream W 0) h a).mp hm
    have hr : a ∈ Set.range (fun j : ℕ =>
        kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (-((j : ℤ) + 1)))) := by
      rw [← kmswRunEventuallyLL_eq_range (shiftedStream W 0) h]
      exact he
    obtain ⟨j, hj⟩ := hr
    obtain ⟨P, hP⟩ := m0Cut_betaL_exists W H h hLL
    left
    refine ⟨P, j, ?_⟩
    rw [hP j]
    have hi : -(j : ℤ) - 1 = -((j : ℤ) + 1) := by omega
    rw [hi]
    exact congrArg (wholePlaneEdgeι W 0) hj




theorem m0Cut_tail_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) (d : ℕ × Bool) :
    m0CutTail W H (wholePlaneDartι W 0 d) ↔
      futureMapTail (shiftedStream W 0) d := by
  classical
  constructor
  · rintro ⟨ht, hm⟩
    have hp : EdgePresent (shiftedStream W 0) d.1 := by
      by_contra hn
      exact hm ((m0Cut_missing_iff W H h hLL d.1).mpr hn)
    refine ⟨?_, hp⟩
    have hb : ¬ d.2 := ht.1
    cases hd : d.2
    · rfl
    · exact (hb hd).elim
  · rintro ⟨hb, hp⟩
    refine ⟨⟨?_, wholePlaneEdgePresent_ι_of_run_present W 0 d.1 hp⟩, ?_⟩
    · change ¬ d.2
      simp only [hb, Bool.false_eq_true, not_false_eq_true]
    · exact fun hm => (m0Cut_missing_iff W H h hLL d.1).mp hm hp




theorem m0Cut_rotation_symm_firstReturn (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : ℕ × Bool) :
    ∃ k : ℕ, 0 < k ∧
      ((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W 0 d) =
        wholePlaneDartι W 0 ((kmswInfRot (shiftedStream W 0) (H.1 0)).symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((wholePlaneRotation W H).symm ^ j) (wholePlaneDartι W 0 d) ∉
          Set.range (wholePlaneDartι W 0) :=
  wholePlaneRotation_symm_firstReturn_run W H 0 d





theorem m0Cut_leftEdgeDarts_eq_runZero (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h) :
    {d : WholePlaneDart W | d.1 ∈ m0CutLeftEdges W H S} =
      Set.range (wholePlaneDartι W 0) := by
  rw [m0Cut_leftEdges_eq_runZero W H h S hS]
  ext d
  constructor
  · rintro ⟨e, he⟩
    exact ⟨(e, d.2), Prod.ext he rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e.1, rfl⟩




@[expose] def m0CutDirectedStep (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
    (u v : WholePlaneVertex W) : Prop :=
  ∃ d : WholePlaneDart W, m0CutTail W H d ∧ d.1 ∈ m0CutLeftEdges W H S ∧
    wholePlaneEdgeWest W d.1 = u ∧ wholePlaneEdgeEast W d.1 = v

section Paths
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (S : WholePlaneEdge W → Prop)
    (hS : ∀ e, S e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h)

include h hLL hS in



theorem m0Cut_directedStep_iff_present (u v : WholePlaneVertex W) :
    m0CutDirectedStep W H S u v ↔
      ∃ a : ℕ, EdgePresent (shiftedStream W 0) a ∧
        wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) a) = u ∧
        wholePlaneVertexι W 0 (edgeEast (shiftedStream W 0) a) = v := by
  constructor
  · rintro ⟨d, ht, he, hu, hv⟩
    rw [m0Cut_leftEdges_eq_runZero W H h S hS] at he
    obtain ⟨a, ha⟩ := he
    have hd : wholePlaneDartι W 0 (a, d.2) = d := Prod.ext ha rfl
    have hp := (m0Cut_tail_iff W H h hLL (a, d.2)).mp (hd.symm ▸ ht)
    refine ⟨a, hp.2, ?_, ?_⟩
    · exact (m0Cut_edgeWest W a).symm.trans ((congrArg (wholePlaneEdgeWest W) ha).trans hu)
    · exact (m0Cut_edgeEast W a).symm.trans ((congrArg (wholePlaneEdgeEast W) ha).trans hv)
  · rintro ⟨a, hp, hu, hv⟩
    refine ⟨wholePlaneDartι W 0 (a, false),
      (m0Cut_tail_iff W H h hLL (a, false)).mpr ⟨rfl, hp⟩, ?_, ?_, ?_⟩
    · rw [m0Cut_leftEdges_eq_runZero W H h S hS]
      exact ⟨a, rfl⟩
    · exact (m0Cut_edgeWest W a).trans hu
    · exact (m0Cut_edgeEast W a).trans hv




@[expose] def m0CutReachableLength {V : Type*} (R : V → V → Prop) :
    ℕ → V → V → Prop
  | 0, u, v => u = v
  | n + 1, u, v => ∃ x, m0CutReachableLength R n u x ∧ R x v

include h hLL hS in



theorem m0Cut_reachableLength_iff_presentPath (n u v : ℕ) :
    m0CutReachableLength (m0CutDirectedStep W H S) n
        (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) ↔
      ∃ p : Quiver.Path (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩,
        p.length = n := by
  induction n generalizing v with
  | zero =>
    constructor
    · intro he
      have huv := wholePlaneVertexι_injective W 0 he
      subst v
      exact ⟨.nil, rfl⟩
    · rintro ⟨p, hp⟩
      have he := congrArg PresentVertex.id (p.eq_of_length_zero hp)
      exact congrArg (wholePlaneVertexι W 0) he
  | succ n ih =>
    constructor
    · rintro ⟨x, hx, hs⟩
      obtain ⟨a, ha, hwest, heast⟩ :=
        (m0Cut_directedStep_iff_present W H h hLL S hS x _).mp hs
      rw [← hwest] at hx
      obtain ⟨p, hp⟩ := (ih (edgeWest (shiftedStream W 0) a)).mp hx
      have hv := wholePlaneVertexι_injective W 0 heast
      let e : (⟨edgeWest (shiftedStream W 0) a⟩ :
          PresentVertex (shiftedStream W 0)) ⟶ ⟨v⟩ := ⟨a, ha, rfl, hv⟩
      exact ⟨p.cons e, by change p.length + 1 = n + 1; rw [hp]⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil =>
        change 0 = n + 1 at hp
        omega
      | @cons b c p e =>
        have hlen : p.length = n := by
          change p.length + 1 = n + 1 at hp
          omega
        refine ⟨wholePlaneVertexι W 0 b.id, (ih b.id).mpr ⟨p, hlen⟩, ?_⟩
        apply (m0Cut_directedStep_iff_present W H h hLL S hS _ _).mpr
        exact ⟨e.val, e.property.1,
          congrArg (wholePlaneVertexι W 0) e.property.2.1,
          congrArg (wholePlaneVertexι W 0) e.property.2.2⟩




@[expose] noncomputable def m0CutSDP (u v : WholePlaneVertex W) : ℕ∞ :=
  ⨅ n : ℕ, ⨅ (_ : m0CutReachableLength (m0CutDirectedStep W H S) n u v), (n : ℕ∞)




@[expose] noncomputable def m0CutLDP (u v : WholePlaneVertex W) : WithBot ℕ∞ :=
  ⨆ n : ℕ, ⨆ (_ : m0CutReachableLength (m0CutDirectedStep W H S) n u v),
    ((n : ℕ∞) : WithBot ℕ∞)

include h hLL hS in



theorem m0Cut_sdp_eq_present (u v : ℕ) :
    m0CutSDP W H S (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) =
      sdp (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩ := by
  apply le_antisymm
  · apply le_iInf
    intro p
    have hp := (m0Cut_reachableLength_iff_presentPath W H h hLL S hS p.length u v).mpr
      ⟨p, rfl⟩
    exact iInf_le_of_le p.length (iInf_le _ hp)
  · apply le_iInf
    intro n
    apply le_iInf
    intro hn
    obtain ⟨p, hp⟩ :=
      (m0Cut_reachableLength_iff_presentPath W H h hLL S hS n u v).mp hn
    rw [← hp]
    exact sdp_le_length p

include h hLL hS in



theorem m0Cut_ldp_eq_present (u v : ℕ) :
    m0CutLDP W H S (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) =
      presentLdp (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩ := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro hn
    obtain ⟨p, hp⟩ :=
      (m0Cut_reachableLength_iff_presentPath W H h hLL S hS n u v).mp hn
    rw [← hp]
    exact le_iSup
      (fun q : Quiver.Path (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩ =>
        ((q.length : ℕ∞) : WithBot ℕ∞)) p
  · apply iSup_le
    intro p
    have hp := (m0Cut_reachableLength_iff_presentPath W H h hLL S hS p.length u v).mpr
      ⟨p, rfl⟩
    exact le_iSup_of_le p.length (le_iSup_of_le hp le_rfl)

end Paths

end DirectedDistances.KMSW
