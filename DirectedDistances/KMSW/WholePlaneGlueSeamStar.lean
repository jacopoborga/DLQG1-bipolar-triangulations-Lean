module

public import DirectedDistances.KMSW.WholePlanePastGlueData
public import DirectedDistances.KMSW.PastFaceSucc
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.KMSW.RunBoundaryStackSets

public section
namespace DirectedDistances.KMSW.WholePlaneGlueSeamStar

open DirectedDistances.PlanarMap Set WholePlanePastGlueData

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "rot0" => kmswInfRot w0 ((And.left H) 0)
local notation "rotp" => kmswInfRot wp (past_finiteIncidence W H)
local notation "vert0" => kmswLimitDartVertex w0
local notation "vertp" => kmswLimitDartVertex wp




theorem star_seam (k : ℤ) :
    {E | wholePlaneDartVertex W E = wholePlaneVertexι W 0 (boundaryVertex w0 h0 k)} =
      wholePlaneDartι W 0 '' {e | vert0 e = boundaryVertex w0 h0 k} ∪
        kmswPastDart W '' {e | vertp e = boundaryVertex wp hp (1 - k)} := by
  have hs : kmswPastVertex W (boundaryVertex wp hp (1 - k)) =
      wholePlaneVertexι W 0 (boundaryVertex w0 h0 k) := by
    simpa only [show 1 - (1 - k) = k by omega] using seam_vertex W h0 hp (1 - k)
  ext E
  constructor
  · intro hE
    rcases dart_cover W E with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · exact Or.inl ⟨d, wholePlaneVertexι_injective W 0
        ((wholePlaneDartVertex_ι W 0 d).symm.trans hE), rfl⟩
    · exact Or.inr ⟨d, kmswPastVertex_injective W
        ((pastDart_vertex W d).symm.trans (hE.trans hs.symm)), rfl⟩
  · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
    · exact (wholePlaneDartVertex_ι W 0 d).trans (congrArg (wholePlaneVertexι W 0) hd)
    · exact (pastDart_vertex W d).trans ((congrArg (kmswPastVertex W) hd).trans hs)




private theorem boundary_darts (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (k : ℤ) (e : ℕ × Bool) (hv : kmswLimitDartVertex w e = boundaryVertex w h k)
    (he : ∃ j : ℤ, e.1 = boundaryOuterEdge w h j) :
    e = (boundaryOuterEdge w h k, false) ∨
      e = (boundaryOuterEdge w h (k - 1), true) := by
  obtain ⟨j, hj⟩ := he
  rcases e with ⟨a, b⟩
  dsimp only at hj
  subst a
  cases b with
  | false =>
    change edgeWest w (boundaryOuterEdge w h j) = _ at hv
    rw [(boundaryOuterEdge_endpoints w h j).1] at hv
    have hjk := boundaryVertex_injective w h hv
    exact Or.inl (by rw [hjk])
  | true =>
    change edgeEast w (boundaryOuterEdge w h j) = _ at hv
    rw [(boundaryOuterEdge_endpoints w h j).2.1] at hv
    have hjk := boundaryVertex_injective w h hv
    exact Or.inr (by rw [show j = k - 1 by omega])




theorem runZero_seam_darts (k : ℤ) (e : ℕ × Bool)
    (hv : vert0 e = boundaryVertex w0 h0 k)
    (he : ∃ j : ℤ, e.1 = boundaryOuterEdge w0 h0 j) :
    e = (boundaryOuterEdge w0 h0 k, false) ∨
      e = (boundaryOuterEdge w0 h0 (k - 1), true) :=
  boundary_darts w0 h0 k e hv he




theorem runZero_seam_darts_incident (k : ℤ) :
    (boundaryOuterEdge w0 h0 k, false) ≠ (boundaryOuterEdge w0 h0 (k - 1), true) ∧
      vert0 (boundaryOuterEdge w0 h0 k, false) = boundaryVertex w0 h0 k ∧
      vert0 (boundaryOuterEdge w0 h0 (k - 1), true) = boundaryVertex w0 h0 k := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hb := congrArg Prod.snd he
    cases hb
  · exact (boundaryOuterEdge_endpoints w0 h0 k).1
  · change edgeEast w0 (boundaryOuterEdge w0 h0 (k - 1)) = _
    simpa only [sub_add_cancel] using (boundaryOuterEdge_endpoints w0 h0 (k - 1)).2.1




theorem past_seam_darts (k : ℤ) (e : ℕ × Bool)
    (hv : vertp e = boundaryVertex wp hp (1 - k))
    (he : ∃ j : ℤ, e.1 = boundaryOuterEdge wp hp j) :
    e = (boundaryOuterEdge wp hp (1 - k), false) ∨
      e = (boundaryOuterEdge wp hp (-k), true) := by
  simpa only [show 1 - k - 1 = -k by omega] using
    boundary_darts wp hp (1 - k) e hv he




theorem past_seam_representatives (k : ℤ) :
    kmswPastDart W (boundaryOuterEdge wp hp (1 - k), false) =
        wholePlaneDartι W 0 (boundaryOuterEdge w0 h0 (k - 1), true) ∧
      kmswPastDart W (boundaryOuterEdge wp hp (-k), true) =
        wholePlaneDartι W 0 (boundaryOuterEdge w0 h0 k, false) := by
  constructor
  · simpa only [wholePlaneDartι, show -(1 - k) = k - 1 by omega] using
      kmswPastDart_seam_match_neg W h0 hp (1 - k)
  · change (kmswPastEdge W (boundaryOuterEdge wp hp (-k)), false) = _
    rw [kmswPastEdge_seam_match_neg W h0 hp (-k), neg_neg]
    rfl




theorem overlap (k : ℤ) :
    (wholePlaneDartι W 0 '' {e | vert0 e = boundaryVertex w0 h0 k}) ∩
        (kmswPastDart W '' {e | vertp e = boundaryVertex wp hp (1 - k)}) =
      {wholePlaneDartι W 0 (boundaryOuterEdge w0 h0 k, false),
        wholePlaneDartι W 0 (boundaryOuterEdge w0 h0 (k - 1), true)} := by
  ext E
  constructor
  · rintro ⟨⟨d, hd, rfl⟩, ⟨e, _, he⟩⟩
    have heedge : kmswPastEdge W e.1 = wholePlaneEdgeι W 0 d.1 :=
      congrArg Prod.fst he
    have hm := (kmswPastEdge_mem_runZero_iff W h0 e.1).mp ⟨d.1, heedge.symm⟩
    obtain ⟨j, hj⟩ := kmswPastSeamEdge_image_boundary W h0 e.1 hm
    have hdedge : d.1 = boundaryOuterEdge w0 h0 j :=
      wholePlaneEdgeι_injective W 0 (heedge.symm.trans hj)
    rcases runZero_seam_darts W h0 k d hd ⟨j, hdedge⟩ with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · intro hE
    rcases Set.mem_insert_iff.mp hE with hE | hE
    · subst E
      have hv := (runZero_seam_darts_incident W h0 k).2.1
      refine ⟨⟨_, hv, rfl⟩, ?_⟩
      refine ⟨(boundaryOuterEdge wp hp (-k), true), ?_,
        (past_seam_representatives W h0 hp k).2⟩
      change edgeEast wp (boundaryOuterEdge wp hp (-k)) = _
      simpa only [show -k + 1 = 1 - k by omega] using
        (boundaryOuterEdge_endpoints wp hp (-k)).2.1
    · have hE' := Set.mem_singleton_iff.mp hE
      subst E
      refine ⟨⟨_, (runZero_seam_darts_incident W h0 k).2.2, rfl⟩, ?_⟩
      exact ⟨(boundaryOuterEdge wp hp (1 - k), false),
        (boundaryOuterEdge_endpoints wp hp (1 - k)).1,
        (past_seam_representatives W h0 hp k).1⟩




private theorem triangle_of_not_outer (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hd : ∀ k : ℤ, d ≠ futureMapBoundaryDart w h k) :
    ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  classical
  have hL : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩
  by_contra ht
  rcases (kmswRunInfDart_boundary_iff_not_triangle w hL hR d).mpr ht with
    ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · have hrange : e ∈ Set.range (fun j : ℕ =>
        kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
      rw [← kmswRunEventuallyLL_eq_range w h]
      exact he
    obtain ⟨j, hj⟩ := hrange
    dsimp only at hj
    apply hd (-((j : ℤ) + 1))
    rw [futureMapBoundaryDart, boundaryOuterEdge_of_negative w h (by omega), hj]
  · have hrange : e ∈ Set.range (fun j : ℕ => kmswRightBoundaryEdge w j) := by
      rw [← kmswRunEventuallyLR_eq_range w h]
      exact he
    obtain ⟨j, hj⟩ := hrange
    dsimp only at hj
    by_cases hj0 : j = 0
    · subst j
      apply hd 0
      rw [futureMapBoundaryDart_zero, ← hj, kmswRightBoundaryEdge_zero]
      rfl
    · apply hd (j : ℤ)
      rw [futureMapBoundaryDart, boundaryOuterEdge_of_positive w h (by omega),
        Int.toNat_natCast, hj]




private theorem flip_not_outer (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (k : ℤ) (q : ℕ × Bool) (hv : kmswLimitDartVertex w q = boundaryVertex w h k)
    (hq : q ≠ (boundaryOuterEdge w h k, false)) :
    ∀ j : ℤ, (q.1, !q.2) ≠ futureMapBoundaryDart w h j := by
  intro j he
  have hf := congrArg (fun e : ℕ × Bool => (e.1, !e.2)) he
  have heq : q = (boundaryOuterEdge w h j, false) := by
    simpa only [futureMapBoundaryDart, Bool.not_not, Bool.not_true] using hf
  rw [heq] at hv
  change edgeWest w (boundaryOuterEdge w h j) = _ at hv
  rw [(boundaryOuterEdge_endpoints w h j).1] at hv
  have hj := boundaryVertex_injective w h hv
  exact hq (hj ▸ heq)




theorem rot_seam_runZero (k : ℤ) (d : ℕ × Bool)
    (hv : vert0 d = boundaryVertex w0 h0 k)
    (hd : rot0 d ≠ (boundaryOuterEdge w0 h0 k, false)) :
    wholePlaneRotation W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (rot0 d) := by
  let q := rot0 d
  have hq : vert0 q = boundaryVertex w0 h0 k :=
    (kmswLimitDartVertex_rot w0 ((And.left H) 0) d).trans hv
  have hn := flip_not_outer w0 h0 k q hq hd
  have hf := wholePlaneFaceSucc_run_of_triangle W H 0 (q.1, !q.2)
    (triangle_of_not_outer w0 h0 (q.1, !q.2) hn)
  have hflip : wholePlaneDartFlip W (wholePlaneDartι W 0 (q.1, !q.2)) =
      wholePlaneDartι W 0 q := by
    change (wholePlaneEdgeι W 0 q.1, !(!q.2)) = (wholePlaneEdgeι W 0 q.1, q.2)
    rw [Bool.not_not]
  have hinf : kmswInfFaceSucc w0 ((And.left H) 0) (q.1, !q.2) = d := by
    change (rot0).symm (q.1, !(!q.2)) = d
    rw [Bool.not_not]
    exact Equiv.symm_apply_apply rot0 d
  change (wholePlaneRotation W H).symm
    (wholePlaneDartFlip W (wholePlaneDartι W 0 (q.1, !q.2))) = _ at hf
  rw [hflip, hinf] at hf
  exact (Equiv.eq_symm_apply (wholePlaneRotation W H)).mp hf.symm




theorem rot_seam_past (k : ℤ) (d : ℕ × Bool)
    (hv : vertp d = boundaryVertex wp hp (1 - k))
    (hd : rotp d ≠ (boundaryOuterEdge wp hp (1 - k), false)) :
    wholePlaneRotation W H (kmswPastDart W d) = kmswPastDart W (rotp d) := by
  let q := rotp d
  have hq : vertp q = boundaryVertex wp hp (1 - k) :=
    (kmswLimitDartVertex_rot wp (past_finiteIncidence W H) d).trans hv
  have hn := flip_not_outer wp hp (1 - k) q hq hd
  have hf := kmswPastDart_faceSucc_of_not_outer W H (past_finiteIncidence W H)
    hp (q.1, !q.2) hn
  have hflip : wholePlaneDartFlip W (kmswPastDart W (q.1, !q.2)) =
      kmswPastDart W q := by
    simpa only [Bool.not_not] using pastDart_flip W (q.1, !q.2)
  have hinf : kmswInfFaceSucc wp (past_finiteIncidence W H) (q.1, !q.2) = d := by
    change (rotp).symm (q.1, !(!q.2)) = d
    rw [Bool.not_not]
    exact Equiv.symm_apply_apply rotp d
  change (wholePlaneRotation W H).symm
    (wholePlaneDartFlip W (kmswPastDart W (q.1, !q.2))) = _ at hf
  rw [hflip, hinf] at hf
  exact (Equiv.eq_symm_apply (wholePlaneRotation W H)).mp hf.symm

end
end DirectedDistances.KMSW.WholePlaneGlueSeamStar
