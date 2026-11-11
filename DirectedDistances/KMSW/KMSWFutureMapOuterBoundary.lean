module

public import DirectedDistances.KMSW.KMSWFutureMapCarrier
public import DirectedDistances.KMSW.BoundaryVertexRange
public import DirectedDistances.KMSW.BoundaryLabelling
public import DirectedDistances.KMSW.LimitExternalFace
import DirectedDistances.KMSW.RunBoundaryStackSets
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.KMSW.StageBoundaryMap

/-! Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.

The geometric external darts include the missing LL edges. Their face-successor
order runs from east to west, decreasing the hit label by one. This identifies
the boundary of the combinatorial future-map carrier; a plane realization and
the source-map law remain separate obligations. The present root edge is not
declared to be a missing frame edge. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open scoped Classical

private theorem boundaryHit_unbounded_left (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : ∀ a : ℤ, ∃ n, L w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
  exact ⟨n, hn.le.trans (min_le_left _ _)⟩

private theorem boundaryHit_unbounded_right (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
  exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩

private theorem external_eventually_word (w : ℕ → Fin 3) (d : ℕ × Bool)
    (hd : limitExternalDart w d) :
    ∃ N, ∀ n ≥ N, d ∈ stageOuterWordVal w n := by
  obtain ⟨N, hN⟩ := hd
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨ha, ho⟩ := hN n hn
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, ha⟩, d.2)
  apply (stageOuterWord_mem_val w n x).mp
  apply (stageOuterWord_mem_iff w n x).mpr
  rcases kmswStage_outer_dart_exactly_one w n x ho with hUL | hUR | hLR | hLL
  · exact Or.inl ⟨((kmswStageULDartsFinset_mem w n x).mp hUL.1).1,
      Or.inl ((kmswStageULDartsFinset_mem w n x).mp hUL.1).2⟩
  · exact Or.inl ⟨((kmswStageURDartsFinset_mem w n x).mp hUR.1).1,
      Or.inr ((kmswStageURDartsFinset_mem w n x).mp hUR.1).2⟩
  · exact Or.inr ⟨((kmswStageLRDartsFinset_mem w n x).mp hLR.1).1,
      Or.inl ((kmswStageLRDartsFinset_mem w n x).mp hLR.1).2⟩
  · exact Or.inr ⟨((kmswStageLLDartsFinset_mem w n x).mp hLL.1).1,
      Or.inr ((kmswStageLLDartsFinset_mem w n x).mp hLL.1).2⟩

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The external side of the edge from `x_k` to `x_{k+1}` is its east dart, -/
@[expose] noncomputable def futureMapBoundaryDart (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ × Bool :=
  (boundaryOuterEdge w h k, true)

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result. -/
theorem futureMapBoundaryDart_zero (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) :
    futureMapBoundaryDart w h 0 = futureMapOuterDart := by
  rw [futureMapBoundaryDart, boundaryOuterEdge_zero]
  rfl

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The dart and its reversal retain the ordered boundary endpoints. -/
theorem futureMapBoundaryDart_endpoints (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    kmswLimitDartVertex w (futureMapBoundaryDart w h k) = boundaryVertex w h (k + 1) ∧
      kmswLimitDartVertex w (futureMapEdgeInv (futureMapBoundaryDart w h k)) =
        boundaryVertex w h k := by
  exact ⟨(boundaryOuterEdge_endpoints w h k).2.1,
    (boundaryOuterEdge_endpoints w h k).1⟩

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result. -/
theorem futureMapBoundaryDart_injective (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : Function.Injective (futureMapBoundaryDart w h) := by
  intro i j hij
  have he := congrArg (kmswLimitDartVertex w) hij
  rw [(futureMapBoundaryDart_endpoints w h i).1,
    (futureMapBoundaryDart_endpoints w h j).1] at he
  have hi := boundaryVertex_injective w h he
  omega

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
Every labelled lower-boundary dart is persistently external, with no -/
theorem futureMapBoundaryDart_external (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) :
    limitExternalDart w (futureMapBoundaryDart w h k) := by
  have hR := boundaryHit_unbounded_right w h
  by_cases hkneg : k ≤ -1
  · exact futureMap_missing_east_external w hR _
      ((boundaryOuterEdge_endpoints w h k).2.2.2 hkneg)
  · by_cases hkpos : 1 ≤ k
    · have he := (limitRightBoundaryEdge_iff w hR (kmswRightBoundaryEdge w k.toNat)).mpr
        ⟨k.toNat, rfl⟩
      obtain ⟨N, hN⟩ := he
      rw [futureMapBoundaryDart, boundaryOuterEdge_of_positive w h hkpos]
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨ha, ho⟩ := hN n hn
      exact ⟨ha, ho.2.2⟩
    · have hk : k = 0 := by omega
      rw [hk, futureMapBoundaryDart_zero]
      exact futureMapOuterDart_external w

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
All persistent external darts, including missing edges, are precisely the -/
theorem futureMap_limitExternalDart_iff_boundaryDart (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    limitExternalDart w d ↔ ∃ k : ℤ, d = futureMapBoundaryDart w h k := by
  constructor
  · intro hd
    have hword := external_eventually_word w d hd
    rcases (kmswRunInfDart_eventually_outer_iff w
      (boundaryHit_unbounded_left w h) (boundaryHit_unbounded_right w h) d).mp hword with
      ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · have hrange : e ∈ Set.range (fun j : ℕ =>
          kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
        rw [← kmswRunEventuallyLL_eq_range w h]
        exact he
      obtain ⟨j, hj⟩ := hrange
      dsimp only at hj
      refine ⟨-((j : ℤ) + 1), ?_⟩
      rw [futureMapBoundaryDart, boundaryOuterEdge_of_negative w h (by omega), hj]
    · have hrange : e ∈ Set.range (fun j : ℕ => kmswRightBoundaryEdge w j) := by
        rw [← kmswRunEventuallyLR_eq_range w h]
        exact he
      obtain ⟨j, hj⟩ := hrange
      dsimp only at hj
      by_cases hj0 : j = 0
      · subst j
        refine ⟨0, ?_⟩
        rw [futureMapBoundaryDart_zero, ← hj, kmswRightBoundaryEdge_zero]
        rfl
      · refine ⟨(j : ℤ), ?_⟩
        rw [futureMapBoundaryDart, boundaryOuterEdge_of_positive w h (by omega),
          Int.toNat_natCast, hj]
  · rintro ⟨k, rfl⟩
    exact futureMapBoundaryDart_external w h k

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
Persistent external membership is preserved by the limiting face successor -/
theorem futureMap_external_faceSucc (d : ℕ × Bool) (hd : limitExternalDart w d) :
    limitExternalDart w (kmswInfFaceSucc w hfin d) := by
  obtain ⟨N, hN⟩ := hd
  obtain ⟨M, hM⟩ := kmswInfFaceSucc_eventually_eq_stage w hfin d
  refine ⟨max N M, fun n hn => ?_⟩
  obtain ⟨ha, ho⟩ := hN n ((le_max_left _ _).trans hn)
  obtain ⟨hb, heq⟩ := hM n ((le_max_right _ _).trans hn)
  have hout : (kmswStageDirectedMap w n).IsOuter
      ((kmswMap w n).faceSucc (⟨d.1, hb⟩, d.2)) := by
    change (kmswMap w n).faceSucc.SameCycle (stageULHeadDart w n)
      ((kmswMap w n).faceSucc (⟨d.1, hb⟩, d.2))
    exact ho.apply_right
  rw [heq]
  exact ⟨((kmswMap w n).faceSucc (⟨d.1, hb⟩, d.2)).1.isLt, hout⟩

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The face successor moves to the opposite endpoint before rotating there. -/
theorem futureMap_faceSucc_vertex (d : ℕ × Bool) :
    kmswLimitDartVertex w (kmswInfFaceSucc w hfin d) =
      kmswLimitDartVertex w (futureMapEdgeInv d) := by
  have hr := kmswLimitDartVertex_rot w hfin
    ((kmswInfRot w hfin).symm (futureMapEdgeInv d))
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The external face successor decreases the boundary-edge index by one; -/
theorem futureMapBoundaryDart_faceSucc (h : BoundaryHitWitnesses w) (k : ℤ) :
    kmswInfFaceSucc w hfin (futureMapBoundaryDart w h k) =
      futureMapBoundaryDart w h (k - 1) := by
  obtain ⟨j, hj⟩ := (futureMap_limitExternalDart_iff_boundaryDart w h _).mp
    (futureMap_external_faceSucc w hfin _ (futureMapBoundaryDart_external w h k))
  have hv := futureMap_faceSucc_vertex w hfin (futureMapBoundaryDart w h k)
  rw [hj, (futureMapBoundaryDart_endpoints w h j).1,
    (futureMapBoundaryDart_endpoints w h k).2] at hv
  have hjk := boundaryVertex_injective w h hv
  have hj' : j = k - 1 := by omega
  rw [hj, hj']

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The inverse external face successor increases the label by one. -/
theorem futureMapBoundaryDart_faceSucc_symm (h : BoundaryHitWitnesses w) (k : ℤ) :
    (kmswInfFaceSucc w hfin).symm (futureMapBoundaryDart w h k) =
      futureMapBoundaryDart w h (k + 1) := by
  apply (kmswInfFaceSucc w hfin).injective
  rw [Equiv.apply_symm_apply, futureMapBoundaryDart_faceSucc]
  congr 1
  omega

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
Every integer iterate follows the ordered boundary enumeration. -/
theorem futureMapBoundaryDart_zpow (h : BoundaryHitWitnesses w) (k z : ℤ) :
    (kmswInfFaceSucc w hfin ^ z) (futureMapBoundaryDart w h k) =
      futureMapBoundaryDart w h (k - z) := by
  induction z using Int.induction_on with
  | zero => simp only [zpow_zero, Equiv.Perm.one_apply, sub_zero]
  | succ n ih =>
    rw [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply, ih,
      futureMapBoundaryDart_faceSucc]
    congr 1
    omega
  | pred n ih =>
    have hn : (-(n : ℤ) - 1) = -1 + -(n : ℤ) := by omega
    rw [hn, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply, ih]
    change (kmswInfFaceSucc w hfin).symm (futureMapBoundaryDart w h (k - -↑n)) = _
    rw [futureMapBoundaryDart_faceSucc_symm]
    congr 1
    omega

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
All persistent external darts constitute the single orbit marked by the -/
theorem futureMap_limitExternalDart_iff_sameCycle (h : BoundaryHitWitnesses w)
    (d : ℕ × Bool) :
    limitExternalDart w d ↔
      (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d := by
  constructor
  · intro hd
    obtain ⟨k, rfl⟩ := (futureMap_limitExternalDart_iff_boundaryDart w h d).mp hd
    refine ⟨-k, ?_⟩
    rw [← futureMapBoundaryDart_zero w h, futureMapBoundaryDart_zpow]
    congr 1
    omega
  · rintro ⟨z, hz⟩
    rw [← futureMapBoundaryDart_zero w h, futureMapBoundaryDart_zpow] at hz
    rw [← hz]
    exact futureMapBoundaryDart_external w h (0 - z)

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The external orbit has exactly one dart for every integer boundary-edge label. -/
theorem futureMap_outerOrbit_iff_existsUnique (h : BoundaryHitWitnesses w)
    (d : ℕ × Bool) :
    (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d ↔
      ∃! k : ℤ, d = futureMapBoundaryDart w h k := by
  rw [← futureMap_limitExternalDart_iff_sameCycle w hfin h d,
    futureMap_limitExternalDart_iff_boundaryDart w h d]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, hk, fun j hj => ?_⟩
    exact futureMapBoundaryDart_injective w h (hj.symm.trans hk)
  · rintro ⟨k, hk, _⟩
    exact ⟨k, hk⟩

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The external dart with east endpoint `x_k` has edge label `k - 1`. -/
theorem futureMap_outerVertex_eq_boundaryVertex (h : BoundaryHitWitnesses w) (k : ℤ) :
    kmswLimitDartVertex w (futureMapBoundaryDart w h (k - 1)) = boundaryVertex w h k := by
  simpa only [sub_add_cancel] using (futureMapBoundaryDart_endpoints w h (k - 1)).1

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The vertices incident to the external orbit are exactly the hit-indexed vertices. -/
theorem futureMap_outerOrbit_vertex_range (h : BoundaryHitWitnesses w) :
    {v | ∃ d : ℕ × Bool,
      (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d ∧
        kmswLimitDartVertex w d = v} = Set.range (boundaryVertex w h) := by
  ext v
  constructor
  · rintro ⟨d, hd, hv⟩
    obtain ⟨k, hk, _⟩ := (futureMap_outerOrbit_iff_existsUnique w hfin h d).mp hd
    refine ⟨k + 1, ?_⟩
    rw [hk, (futureMapBoundaryDart_endpoints w h k).1] at hv
    exact hv
  · rintro ⟨k, rfl⟩
    refine ⟨futureMapBoundaryDart w h (k - 1), ?_,
      futureMap_outerVertex_eq_boundaryVertex w h k⟩
    exact (futureMap_limitExternalDart_iff_sameCycle w hfin h _).mp
      (futureMapBoundaryDart_external w h (k - 1))

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The missing-edge outer-orbit field for the raw future-map carrier. -/
theorem futureMap_missing_outer (h : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hm : futureMapMissing w d) :
    Equiv.Perm.SameCycle ((kmswInfRot w hfin).symm * futureMapEdgeInv)
        futureMapOuterDart d ∨
      Equiv.Perm.SameCycle ((kmswInfRot w hfin).symm * futureMapEdgeInv)
        futureMapOuterDart (futureMapEdgeInv d) := by
  rcases futureMap_missing_limitExternalDart w (boundaryHit_unbounded_right w h) d hm
      with hd | hd
  · exact Or.inl ((futureMap_limitExternalDart_iff_sameCycle w hfin h d).mp hd)
  · exact Or.inr ((futureMap_limitExternalDart_iff_sameCycle w hfin h _).mp hd)

/-- Helper toward Theorem 1.4 (thm-busemann, F1); not a paper result.
The locally finite rooted-map fields without any frame: geometric reversal,
missing and tail tags, outer orbit, local finiteness, connectedness and acyclicity. -/
theorem futureMap_withoutFrame_fields (h : BoundaryHitWitnesses w) :
    Countable (ℕ × Bool) ∧
      (∀ d, futureMapEdgeInv (futureMapEdgeInv d) = d) ∧
      (∀ d, futureMapEdgeInv d ≠ d) ∧
      (∀ d, futureMapMissing w d ↔ futureMapMissing w (futureMapEdgeInv d)) ∧
      (∀ d, ¬ futureMapMissing w d →
        (futureMapTail w d ↔ ¬ futureMapTail w (futureMapEdgeInv d))) ∧
      (∀ d, futureMapMissing w d → ¬ futureMapTail w d) ∧
      (∀ d, futureMapMissing w d →
        Equiv.Perm.SameCycle ((kmswInfRot w hfin).symm * futureMapEdgeInv)
            futureMapOuterDart d ∨
          Equiv.Perm.SameCycle ((kmswInfRot w hfin).symm * futureMapEdgeInv)
            futureMapOuterDart (futureMapEdgeInv d)) ∧
      (∀ d, {e : ℕ × Bool | (kmswInfRot w hfin).SameCycle d e}.Finite) ∧
      (∀ d e, Relation.ReflTransGen
        (fun x y : ℕ × Bool => y = kmswInfRot w hfin x ∨
          y = (kmswInfRot w hfin).symm x ∨ y = futureMapEdgeInv x ∨
            y = futureMapEdgeInv.symm x) d e) ∧
      (∀ v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin),
        ¬ Relation.TransGen
          (rootedLocallyFiniteDirectedStep (kmswInfRot w hfin) futureMapEdgeInv
            (futureMapMissing w) (futureMapTail w)) v v) := by
  exact ⟨inferInstance, futureMapEdgeInv_invol, futureMapEdgeInv_ne,
    futureMapMissing_edgeInv w, futureMapTail_iff w, futureMapTail_missing w,
    futureMap_missing_outer w hfin h, futureMap_locallyFinite w hfin,
    futureMap_connected w hfin, futureMap_acyclic w hfin⟩

end DirectedDistances.KMSW
