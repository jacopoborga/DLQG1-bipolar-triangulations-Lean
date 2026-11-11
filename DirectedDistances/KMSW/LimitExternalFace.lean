module

public import DirectedDistances.KMSW.PathSpaceTransferCarrier








public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory DirectedDistances.RandomWalk
open scoped Classical




@[expose] def limitExternalDart (w : ℕ → Fin 3) (d : ℕ × Bool) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∃ h : d.1 < (kmswStage w n).nextEdge,
    (kmswStageDirectedMap w n).IsOuter (⟨d.1, h⟩, d.2)




@[expose] def limitLeftBoundaryEdge (w : ℕ → Fin 3) (e : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∃ h : e < (kmswStage w n).nextEdge,
    (⟨e, h⟩, false) ∈ (kmswStageDirectedMap w n).ulDarts




@[expose] def limitRightBoundaryEdge (w : ℕ → Fin 3) (e : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∃ h : e < (kmswStage w n).nextEdge,
    (⟨e, h⟩, true) ∈ (kmswStageDirectedMap w n).lrDarts

private theorem ul_bound (w : ℕ → Fin 3) {n e : ℕ}
    (he : e ∈ (kmswStage w n).UL) : e < (kmswStage w n).nextEdge :=
  (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl he)))

private theorem lr_bound (w : ℕ → Fin 3) {n e : ℕ}
    (he : e ∈ (kmswStage w n).LR) : e < (kmswStage w n).nextEdge :=
  (kmswStage_boundary_ids_lt_nextEdge w n).2 e (List.mem_append_right _ he)




theorem limitLeftBoundaryEdge_iff (w : ℕ → Fin 3)
    (htrans : Tendsto (L w) atTop atTop) (e : ℕ) :
    limitLeftBoundaryEdge w e ↔ ∃ i, e = kmswLeftBoundaryEdge w i := by
  constructor
  · rintro ⟨N, hN⟩
    apply (isLeftBoundaryEdge_iff w htrans e).mp
    apply Set.Infinite.mono (s := Set.Ici N) ?_ (Set.Ici_infinite N)
    intro n hn
    obtain ⟨h, ho⟩ := hN n hn
    exact (kmswStageDirectedMap_UL_bridge w n ⟨e, h⟩).mpr ho
  · rintro ⟨i, rfl⟩
    obtain ⟨N, hN⟩ := kmswStage_UL_getElem?_eventually w htrans i
    refine ⟨N, fun n hn => ?_⟩
    have hm := List.mem_of_getElem? (hN n hn)
    exact ⟨ul_bound w hm, (kmswStageDirectedMap_UL_bridge w n _).mp hm⟩




theorem limitRightBoundaryEdge_iff (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (e : ℕ) :
    limitRightBoundaryEdge w e ↔ ∃ i, e = kmswRightBoundaryEdge w i := by
  constructor
  · rintro ⟨N, hN⟩
    apply (isRightBoundaryEdge_iff w hR e).mp
    apply Set.Infinite.mono (s := Set.Ici N) ?_ (Set.Ici_infinite N)
    intro n hn
    obtain ⟨h, ho⟩ := hN n hn
    exact (kmswStageDirectedMap_LR_bridge w n ⟨e, h⟩).mpr ho
  · rintro ⟨i, rfl⟩
    obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually w hR i
    refine ⟨N, fun n hn => ?_⟩
    have hm := List.mem_of_getElem? (hN n hn)
    exact ⟨lr_bound w hm, (kmswStageDirectedMap_LR_bridge w n _).mp hm⟩




theorem limitLeftBoundaryEdge_iff_infinite (w : ℕ → Fin 3)
    (htrans : Tendsto (L w) atTop atTop) (e : ℕ) :
    limitLeftBoundaryEdge w e ↔ IsLeftBoundaryEdge w e :=
  (limitLeftBoundaryEdge_iff w htrans e).trans (isLeftBoundaryEdge_iff w htrans e).symm




theorem limitRightBoundaryEdge_iff_infinite (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (e : ℕ) :
    limitRightBoundaryEdge w e ↔ IsRightBoundaryEdge w e :=
  (limitRightBoundaryEdge_iff w hR e).trans (isRightBoundaryEdge_iff w hR e).symm

private theorem outer_ul (w : ℕ → Fin 3) (n e : ℕ)
    (h : e < (kmswStage w n).nextEdge) (hp : (kmswStage w n).present e = true)
    (ho : (kmswStageDirectedMap w n).IsOuter (⟨e, h⟩, false)) :
    (⟨e, h⟩, false) ∈ (kmswStageDirectedMap w n).ulDarts := by
  refine ⟨?_, ⟨hp, rfl⟩, ho⟩
  change ¬ (kmswStage w n).present e = false
  rw [hp]
  decide

private theorem outer_lr (w : ℕ → Fin 3) (n e : ℕ)
    (h : e < (kmswStage w n).nextEdge) (hp : (kmswStage w n).present e = true)
    (ho : (kmswStageDirectedMap w n).IsOuter (⟨e, h⟩, true)) :
    (⟨e, h⟩, true) ∈ (kmswStageDirectedMap w n).lrDarts := by
  refine ⟨?_, ?_, ho⟩
  · change ¬ (kmswStage w n).present e = false
    rw [hp]
    decide
  · rintro ⟨_, hbad⟩
    exact Bool.noConfusion hbad




theorem limitExternalDart_iff (w : ℕ → Fin 3)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (d : ℕ × Bool) :
    limitExternalDart w d ↔
      (∃ i, d = (kmswLeftBoundaryEdge w i, false)) ∨
      (∃ i, d = (kmswRightBoundaryEdge w i, true)) := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨M, hM⟩ := eventually_present_of_nonneg_of_unbounded w hL0 hR d.1
    rcases d with ⟨e, b⟩
    cases b with
    | false =>
      left
      have he : limitLeftBoundaryEdge w e := by
        refine ⟨max N M, fun n hn => ?_⟩
        obtain ⟨h, ho⟩ := hN n ((le_max_left _ _).trans hn)
        exact ⟨h, outer_ul w n e h (hM n ((le_max_right _ _).trans hn)).2 ho⟩
      obtain ⟨i, hi⟩ := (limitLeftBoundaryEdge_iff w htrans e).mp he
      exact ⟨i, Prod.ext hi rfl⟩
    | true =>
      right
      have he : limitRightBoundaryEdge w e := by
        refine ⟨max N M, fun n hn => ?_⟩
        obtain ⟨h, ho⟩ := hN n ((le_max_left _ _).trans hn)
        exact ⟨h, outer_lr w n e h (hM n ((le_max_right _ _).trans hn)).2 ho⟩
      obtain ⟨i, hi⟩ := (limitRightBoundaryEdge_iff w hR e).mp he
      exact ⟨i, Prod.ext hi rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · obtain ⟨N, hN⟩ := (limitLeftBoundaryEdge_iff w htrans _).mpr ⟨i, rfl⟩
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨h, ho⟩ := hN n hn
      exact ⟨h, ho.2.2⟩
    · obtain ⟨N, hN⟩ := (limitRightBoundaryEdge_iff w hR _).mpr ⟨i, rfl⟩
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨h, ho⟩ := hN n hn
      exact ⟨h, ho.2.2⟩

private theorem outer_mem_word (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present d.1.val = true)
    (ho : (kmswStageDirectedMap w n).IsOuter d) : d ∈ stageOuterWord w n := by
  rcases d with ⟨⟨e, h⟩, b⟩
  apply (stageOuterWord_mem_iff w n _).mpr
  cases b with
  | false =>
    exact Or.inl ⟨rfl, Or.inl ((kmswStageDirectedMap_UL_bridge w n _).mpr
      (outer_ul w n e h hp ho))⟩
  | true =>
    exact Or.inr ⟨rfl, Or.inl ((kmswStageDirectedMap_LR_bridge w n _).mpr
      (outer_lr w n e h hp ho))⟩

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

include hfin in



theorem not_limitExternalDart_eventually_triangle
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (d : ℕ × Bool) (hd : ¬ limitExternalDart w d) :
    ∃ j : TriangleCreationTime w, ∃ N, ∀ n, N ≤ n → ∃ hj : j.val < n,
      ∃ h : d.1 < (kmswStage w n).nextEdge,
        d ∈ stageTriangleDartList w j ∧
        FaceSucc3Cycle (kmswMap w n).faceSucc
          (stageTriangleDart₁ w n j hj) (stageTriangleDart₂ w n j hj)
          (stageTriangleDart₃ w n j hj) ∧
        ¬ (kmswStageDirectedMap w n).IsOuter (⟨d.1, h⟩, d.2) := by
  have hb := (limitExternalDart_iff w htrans hR hL0 d).not.mp hd
  obtain ⟨j, ⟨hdj, _⟩, _⟩ := kmswInfDart_nonOuterFace_cycle w hfin htrans hR hL0 d
    (fun i hi => hb (Or.inl ⟨i, hi⟩)) (fun i hi => hb (Or.inr ⟨i, hi⟩))
  obtain ⟨M, hM⟩ := eventually_present_of_nonneg_of_unbounded w hL0 hR d.1
  refine ⟨j, max (j.val + 1) M, fun n hn => ?_⟩
  have hj : j.val < n := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans hn)
  have hp := hM n ((le_max_right _ _).trans hn)
  refine ⟨hj, hp.1, hdj, stageTriangle_isFace w j n hj, fun ho => ?_⟩
  exact stageTriangleDart_not_outer w n j hj (⟨d.1, hp.1⟩, d.2) hdj
    (outer_mem_word w n _ hp.2 ho)




theorem limitExternalDart_iff_sameCycle (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) (d : ℕ × Bool) :
    limitExternalDart w d ↔ (kmswInfFaceSucc w hfin).SameCycle
      (kmswLeftBoundaryEdge w 0, false) d := by
  let f := kmswInfFaceSucc w hfin
  have hj := mapBoundary_junction w hfin htrans hR hL0
  rw [limitExternalDart_iff w htrans hR hL0 d]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨(i : ℤ), ?_⟩
      simpa only [zpow_natCast, Equiv.Perm.coe_pow] using
        mapLeftBoundary_iterate w hfin htrans i
    · have hjoin : f.SameCycle (kmswRightBoundaryEdge w 0, true)
          (kmswLeftBoundaryEdge w 0, false) := ⟨1, by simpa only [zpow_one] using hj⟩
      have hright : (f⁻¹).SameCycle (kmswRightBoundaryEdge w 0, true)
          (kmswRightBoundaryEdge w i, true) := by
        refine ⟨(i : ℤ), ?_⟩
        simpa only [zpow_natCast, Equiv.Perm.coe_pow, Equiv.Perm.inv_def, f] using
          mapRightBoundary_iterate w hfin hL0 hR i
      exact hjoin.symm.trans hright.of_inv
  · rintro ⟨z, hz⟩
    cases z with
    | ofNat i =>
      left
      have hi := mapLeftBoundary_iterate w hfin htrans i
      have hz' : f^[i] (kmswLeftBoundaryEdge w 0, false) = d := by
        change (f ^ (i : ℤ)) (kmswLeftBoundaryEdge w 0, false) = d at hz
        simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hz
      exact ⟨i, hz'.symm.trans hi⟩
    | negSucc i =>
      right
      have hji : f.symm (kmswLeftBoundaryEdge w 0, false) =
          (kmswRightBoundaryEdge w 0, true) := f.symm_apply_eq.mpr hj.symm
      have hi : f.symm^[i + 1] (kmswLeftBoundaryEdge w 0, false) =
          (kmswRightBoundaryEdge w i, true) := by
        rw [Function.iterate_succ_apply, hji]
        exact mapRightBoundary_iterate w hfin hL0 hR i
      have hz' : f.symm^[i + 1] (kmswLeftBoundaryEdge w 0, false) = d := by
        simpa only [f, zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow,
          Equiv.Perm.inv_def] using hz
      exact ⟨i, hz'.symm.trans hi⟩




theorem limitExternalDart_faceSucc (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) (d : ℕ × Bool) :
    (limitExternalDart w (kmswInfFaceSucc w hfin d) ↔ limitExternalDart w d) ∧
      (limitExternalDart w ((kmswInfFaceSucc w hfin).symm d) ↔
        limitExternalDart w d) := by
  simp only [limitExternalDart_iff_sameCycle w hfin htrans hR hL0,
    Equiv.Perm.sameCycle_apply_right, Equiv.Perm.sameCycle_symm_apply_right, and_self]




theorem mapLeftBoundaryVertex_iff_limit (htrans : Tendsto (L w) atTop atTop) (v : ℕ) :
    mapLeftBoundaryVertex w hfin v ↔ ∃ e, limitLeftBoundaryEdge w e ∧
      (edgeWest w e = v ∨ edgeEast w e = v) := by
  rw [mapLeftBoundaryVertex_iff w hfin htrans]
  exact exists_congr (fun e => and_congr
    (limitLeftBoundaryEdge_iff_infinite w htrans e).symm Iff.rfl)




theorem mapRightBoundaryVertex_iff_limit (hL0 : ∀ j, 0 ≤ L w j)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) :
    mapRightBoundaryVertex w hfin v ↔ ∃ e, limitRightBoundaryEdge w e ∧
      (edgeWest w e = v ∨ edgeEast w e = v) := by
  rw [mapRightBoundaryVertex_iff w hfin hL0 hR]
  exact exists_congr (fun e => and_congr
    (limitRightBoundaryEdge_iff_infinite w hR e).symm Iff.rfl)





theorem conditionedVectorPathLaw_ae_unique_limitExternalFace :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        (∀ e, (limitLeftBoundaryEdge w e ↔ ∃ i, e = kmswLeftBoundaryEdge w i) ∧
          (limitRightBoundaryEdge w e ↔ ∃ i, e = kmswRightBoundaryEdge w i) ∧
          (limitLeftBoundaryEdge w e ↔ IsLeftBoundaryEdge w e) ∧
          (limitRightBoundaryEdge w e ↔ IsRightBoundaryEdge w e)) ∧
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          (∀ d : ℕ × Bool,
            (limitExternalDart w d ↔
              (∃ i, d = (kmswLeftBoundaryEdge w i, false)) ∨
              (∃ i, d = (kmswRightBoundaryEdge w i, true))) ∧
            (limitExternalDart w d ↔ (kmswInfFaceSucc w hfin).SameCycle
              (kmswLeftBoundaryEdge w 0, false) d) ∧
            (limitExternalDart w (kmswInfFaceSucc w hfin d) ↔ limitExternalDart w d) ∧
            (limitExternalDart w ((kmswInfFaceSucc w hfin).symm d) ↔
              limitExternalDart w d) ∧
            (¬ limitExternalDart w d →
              ∃ j : TriangleCreationTime w, ∃ N, ∀ n, N ≤ n → ∃ hj : j.val < n,
                ∃ h : d.1 < (kmswStage w n).nextEdge,
                  d ∈ stageTriangleDartList w j ∧
                  FaceSucc3Cycle (kmswMap w n).faceSucc
                    (stageTriangleDart₁ w n j hj) (stageTriangleDart₂ w n j hj)
                    (stageTriangleDart₃ w n j hj) ∧
                  ¬ (kmswStageDirectedMap w n).IsOuter (⟨d.1, h⟩, d.2))) ∧
          (∀ v : ℕ,
            (mapLeftBoundaryVertex w hfin v ↔ ∃ e, limitLeftBoundaryEdge w e ∧
              (edgeWest w e = v ∨ edgeEast w e = v)) ∧
            (mapRightBoundaryVertex w hfin v ↔ ∃ e, limitRightBoundaryEdge w e ∧
              (edgeWest w e = v ∨ edgeEast w e = v))) := by
  filter_upwards [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hp
  obtain ⟨w, hwp, hfin, htrans, hR, hL0, _, _⟩ := hp
  refine ⟨w, ⟨hwp, ?_, hfin, ?_, ?_⟩, ?_⟩
  · intro e
    exact ⟨limitLeftBoundaryEdge_iff w htrans e, limitRightBoundaryEdge_iff w hR e,
      limitLeftBoundaryEdge_iff_infinite w htrans e,
      limitRightBoundaryEdge_iff_infinite w hR e⟩
  · intro d
    have hc := limitExternalDart_faceSucc w hfin htrans hR hL0 d
    exact ⟨limitExternalDart_iff w htrans hR hL0 d,
      limitExternalDart_iff_sameCycle w hfin htrans hR hL0 d, hc.1, hc.2,
      not_limitExternalDart_eventually_triangle w hfin htrans hR hL0 d⟩
  · intro v
    exact ⟨mapLeftBoundaryVertex_iff_limit w hfin htrans v,
      mapRightBoundaryVertex_iff_limit w hfin hL0 hR v⟩
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

end DirectedDistances.KMSW
