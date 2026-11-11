/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondenceFull
public import DirectedDistances.PaperProofs.Section5.UIBHBOTSourceChainExhaustion
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.RandomWalk.ExcursionBlockUniformTail

/-! # Created triangle face cycles for the UIBHBOT

The deterministic cycle statements require only `WholePlaneRotationHypothesis`:
the boundary-hit witnesses are not needed to preserve an already created face.
All geometric darts, including darts of missing edges, are retained. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open WholePlaneGlueFaceCorrespondenceFull
open scoped Classical



theorem wholePlaneDartι_injective (W : ℤ → Fin 3) (N : ℕ) :
    Function.Injective (wholePlaneDartι W N) := by
  intro a b hab
  apply Prod.ext
  · exact wholePlaneEdgeι_injective W N (congrArg Prod.fst hab)
  · exact congrArg (fun d : WholePlaneDart W => d.2) hab





theorem wholePlane_stageTriangle_faceSucc_cycle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) :
    FaceSucc3Cycle (wholePlaneFaceSucc W H)
      (wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) j).1)
      (wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) j).2.1)
      (wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) j).2.2) := by
  let t := stageTriangleDartTriple (shiftedStream W N) j
  have hc := kmswInfFaceSucc_stageTriangle_cycle (shiftedStream W N) (H.1 N) j
  have hfirst : t.1 ∈ stageTriangleDartList (shiftedStream W N) j := by
    simp only [stageTriangleDartList, t, List.mem_cons, List.not_mem_nil, or_false,
      true_or]
  have hsecond : t.2.1 ∈ stageTriangleDartList (shiftedStream W N) j := by
    simp only [stageTriangleDartList, t, List.mem_cons, List.not_mem_nil, or_false,
      true_or, or_true]
  have hthird : t.2.2 ∈ stageTriangleDartList (shiftedStream W N) j := by
    simp only [stageTriangleDartList, t, List.mem_cons, List.not_mem_nil, or_false,
      or_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (wholePlaneFaceSucc_run_of_triangle W H N t.1 ⟨j, hfirst⟩).trans
      (congrArg (wholePlaneDartι W N) hc.1)
  · exact (wholePlaneFaceSucc_run_of_triangle W H N t.2.1 ⟨j, hsecond⟩).trans
      (congrArg (wholePlaneDartι W N) hc.2.1)
  · exact (wholePlaneFaceSucc_run_of_triangle W H N t.2.2 ⟨j, hthird⟩).trans
      (congrArg (wholePlaneDartι W N) hc.2.2.1)
  · exact fun he => hc.2.2.2.1 (wholePlaneDartι_injective W N he)
  · exact fun he => hc.2.2.2.2.1 (wholePlaneDartι_injective W N he)
  · exact fun he => hc.2.2.2.2.2 (wholePlaneDartι_injective W N he)



private theorem faceSucc_threeCycle_sameCycle_iff {D : Type*} (f : Equiv.Perm D)
    (a b c : D) (hc : FaceSucc3Cycle f a b c) (e : D) :
    f.SameCycle a e ↔ e = a ∨ e = b ∨ e = c := by
  have hmem (z : ℤ) : (f ^ z) a = a ∨ (f ^ z) a = b ∨ (f ^ z) a = c := by
    induction z using Int.induction_on with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      rcases ih with ha | hb | hd
      · exact Or.inr (Or.inl ((congrArg f ha).trans hc.1))
      · exact Or.inr (Or.inr ((congrArg f hb).trans hc.2.1))
      · exact Or.inl ((congrArg f hd).trans hc.2.2.1)
    | pred n ih =>
      rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      rcases ih with ha | hb | hd
      · exact Or.inr (Or.inr ((congrArg f.symm ha).trans
          ((f.symm_apply_eq).mpr hc.2.2.1.symm)))
      · exact Or.inl ((congrArg f.symm hb).trans ((f.symm_apply_eq).mpr hc.1.symm))
      · exact Or.inr (Or.inl ((congrArg f.symm hd).trans
          ((f.symm_apply_eq).mpr hc.2.1.symm)))
  constructor
  · rintro ⟨z, rfl⟩
    exact hmem z
  · rintro (rfl | rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simpa only [zpow_one] using hc.1⟩
    · exact ⟨2, by simpa only [show (2 : ℤ) = 1 + 1 by omega,
        zpow_add, zpow_one, Equiv.Perm.mul_apply, hc.1] using hc.2.1⟩



theorem wholePlane_stageTriangle_sameCycle_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) (d : WholePlaneDart W) :
    (wholePlaneFaceSucc W H).SameCycle
        (wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) j).1) d ↔
      d ∈ wholePlaneDartι W N ''
        {a | a ∈ stageTriangleDartList (shiftedStream W N) j} := by
  rw [faceSucc_threeCycle_sameCycle_iff _ _ _ _
    (wholePlane_stageTriangle_faceSucc_cycle W H N j)]
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
  · rintro ⟨a, (rfl | rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)



theorem wholePlane_stageTriangle_darts_card (W : ℤ → Fin 3) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) :
    ((stageTriangleDartList (shiftedStream W N) j).toFinset.image
      (wholePlaneDartι W N)).card = 3 := by
  rw [Finset.card_image_of_injective _ (wholePlaneDartι_injective W N),
    List.toFinset_card_of_nodup (stageTriangleDartList_nodup _ j)]
  rfl



private theorem active_east_triangle_of_nonrecord (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (h : BoundaryHitWitnesses w) (k : ℕ)
    (hi : ∃ i ≤ k, R w i < R w k) :
    ∃ j : TriangleCreationTime w, (act w k, true) ∈ stageTriangleDartList w j := by
  have hL : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  rcases kmswRunInfDart_partition w hfin hL h.R_unbounded_below (act w k, true) with
    ⟨e, ⟨n, hn⟩, he⟩ | ⟨e, ⟨n, hn⟩, he⟩ | ⟨j, hj, _⟩
  · have he' : act w k = e := congrArg Prod.fst he
    have halloc := (kmswStage_active_lt w k).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_max_left k n))
    have hp : (kmswStage w k).present (act w k) = true := by
      apply (kmswStage_status w k).2.1
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last w k
      rw [hxs]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hp' := (present_mono w (kmswStage_active_lt w k) hp
      (max k n) (Nat.le_max_left k n)).2
    have hLL := hn (max k n) (Nat.le_max_right k n)
    rw [← he'] at hLL
    have hm := ((kmswStage_status w (max k n)).1 _ halloc).mpr (Or.inr hLL)
    rw [hp'] at hm
    cases hm
  · have he' : act w k = e := congrArg Prod.fst he
    have hmem := hn n le_rfl
    rw [kmswStage_LR_eq] at hmem
    obtain ⟨m, hm, hme⟩ := List.mem_map.mp hmem
    have hmk : m = k := CutConverse.act_injective w (hme.trans he'.symm)
    subst m
    have hrec : ∀ i < k, R w k < R w i :=
      of_decide_eq_true (List.mem_filter.mp hm).2
    obtain ⟨i, hik, hRi⟩ := hi
    by_cases hik' : i < k
    · exact (lt_asymm hRi (hrec i hik')).elim
    · have heq : i = k := by omega
      exact (lt_irrefl _ (heq ▸ hRi)).elim
  · exact ⟨j, hj⟩



private theorem faceTriangles_trans_act (W : ℤ → Fin 3) (N M : ℕ)
    (hNM : N ≤ M) (k : ℕ) :
    wholePlaneEdgeTrans W N M hNM (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  have hact (w : ℕ → Fin 3) (s k : ℕ) :
      kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
    unfold act
    rw [kmswWindowEdgeMapInf_eq_stage w s k _
      (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
    exact (kmswWindowPatchData_rel w s k).active
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M hNM] using
    hact (shiftedStream W M) (M - N) k



private theorem uibhbotCodeLawRel_ae_vertical_nonrecord :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
        ∃ i ≤ (t + (M : ℤ)).toNat,
          R (shiftedStream W M) i < R (shiftedStream W M) (t + (M : ℤ)).toNat := by
  have hR (M i : ℕ) : Measurable (fun W : ℤ → Fin 3 => R (shiftedStream W M) i) :=
    (measurable_to_countable' (fun a => measurableSet_R i (fun b => b = a))).comp
      (measurable_pi_iff.mpr (fun j => measurable_pi_apply ((j : ℤ) - M)))
  have hm : MeasurableSet {W : ℤ → Fin 3 |
      ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ i ≤ (t + (M : ℤ)).toNat,
        R (shiftedStream W M) i < R (shiftedStream W M) (t + (M : ℤ)).toNat} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    refine MeasurableSet.iInter fun t => MeasurableSet.iUnion fun M₀ =>
      MeasurableSet.iInter fun M => MeasurableSet.iInter fun _ =>
        MeasurableSet.iUnion fun i => ?_
    by_cases hi : i ≤ (t + (M : ℤ)).toNat
    · simpa only [hi, true_and] using
        measurableSet_lt (hR M i) (hR M (t + (M : ℤ)).toNat)
    · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel, _
  apply (ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable hm).mpr
  filter_upwards [uibhbotWordFamilyLaw_ae_hP2] with w hw
  obtain ⟨hw, hP⟩ := hw
  rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
  intro t
  obtain ⟨M₀, hM₀⟩ := hP t
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨i, hi, he⟩ := runningMin_attained
    (R (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M))
    (t + (M : ℤ)).toNat
  exact ⟨i, hi, he ▸ (hM₀ M hM).2⟩




private theorem present_east_dart_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (hback : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ∃ i ≤ (t + (M : ℤ)).toNat,
        R (shiftedStream W M) i < R (shiftedStream W M) (t + (M : ℤ)).toNat)
    (e : WholePlaneEdge W) (hp : wholePlaneEdgePresent W e) :
    ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
      (e, true) ∈ wholePlaneDartι W N ''
        {d | d ∈ stageTriangleDartList (shiftedStream W N) j} := by
  obtain ⟨⟨N, a⟩, rfl⟩ := Quotient.exists_rep e
  obtain ⟨M, hNM, hM⟩ := (wholePlaneEdgePresent_ι W N a).mp hp
  obtain ⟨n, hn, hp⟩ := hM M le_rfl
  obtain ⟨k, _, hk⟩ := kmswStage_present_eq_active (shiftedStream W M) n _ hn hp
  change act (shiftedStream W M) k = wholePlaneEdgeTrans W N M hNM a at hk
  obtain ⟨B, hB⟩ := hback ((k : ℤ) - M)
  let K := max M B
  have hMK : M ≤ K := Nat.le_max_left _ _
  have hindex : ((k : ℤ) - M + (K : ℤ)).toNat = K - M + k := by omega
  have hnonrec := hB K (Nat.le_max_right M B)
  rw [hindex] at hnonrec
  obtain ⟨j, hj⟩ := active_east_triangle_of_nonrecord (shiftedStream W K)
    (H.1 K) (hhit K) (K - M + k) hnonrec
  refine ⟨K, j, (act (shiftedStream W K) (K - M + k), true), hj, ?_⟩
  apply Prod.ext
  · change wholePlaneEdgeι W K (act (shiftedStream W K) (K - M + k)) =
      wholePlaneEdgeι W N a
    rw [← faceTriangles_trans_act W M K hMK k, hk]
    have hc := congrFun (wholePlaneEdgeTrans_comp W N M K hNM hMK) a
    change wholePlaneEdgeTrans W M K hMK (wholePlaneEdgeTrans W N M hNM a) =
      wholePlaneEdgeTrans W N K (hNM.trans hMK) a at hc
    rw [hc]
    exact congrFun (wholePlaneEdgeι_trans W N K (hNM.trans hMK)) a
  · rfl



private theorem west_dart_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N)) (e : WholePlaneEdge W) :
    ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
      (e, false) ∈ wholePlaneDartι W N ''
        {d | d ∈ stageTriangleDartList (shiftedStream W N) j} := by
  obtain ⟨⟨N, a⟩, rfl⟩ := Quotient.exists_rep e
  rcases dart_outer_or_creation (shiftedStream W N) (H.1 N) (hhit N) (a, false) with
    ⟨ho, _⟩ | ⟨⟨j, hj⟩, _⟩
  · obtain ⟨k, hk, _⟩ := (futureMap_outerOrbit_iff_existsUnique
      (shiftedStream W N) (H.1 N) (hhit N) (a, false)).mp ho
    have hb := congrArg Prod.snd hk
    change false = true at hb
    cases hb
  · exact ⟨N, j, (a, false), hj, rfl⟩



theorem wholePlane_missing_east_not_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (e : WholePlaneEdge W) (hm : ¬ wholePlaneEdgePresent W e) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) :
    (e, true) ∉ wholePlaneDartι W N ''
      {d | d ∈ stageTriangleDartList (shiftedStream W N) j} := by
  rintro ⟨⟨a, b⟩, ha, hea⟩
  have hb : b = true := congrArg (fun d : WholePlaneDart W => d.2) hea
  subst b
  have he : wholePlaneEdgeι W N a = e := congrArg Prod.fst hea
  have hmissing : ¬ EdgePresent (shiftedStream W N) a := by
    intro hp
    exact hm (he ▸ wholePlaneEdgePresent_ι_of_run_present W N a hp)
  have hexternal := futureMap_missing_east_external (shiftedStream W N)
    (hhit N).R_unbounded_below a hmissing
  exact creation_dart_not_outer (shiftedStream W N) (H.1 N) (hhit N) j (a, true) ha
    ((futureMap_limitExternalDart_iff_sameCycle
      (shiftedStream W N) (H.1 N) (hhit N) (a, true)).mp hexternal)



theorem wholePlane_stageTriangle_not_outer (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) (d : WholePlaneDart W)
    (hd : d ∈ wholePlaneDartι W N ''
      {a | a ∈ stageTriangleDartList (shiftedStream W N) j}) :
    ¬ (wholePlaneFaceSucc W H).SameCycle (uibhbotWholePlaneOuterDart W) d := by
  intro ho
  have ht := (wholePlane_stageTriangle_sameCycle_iff W H N j d).mpr hd
  have hr := (wholePlane_stageTriangle_sameCycle_iff W H N j
    (uibhbotWholePlaneOuterDart W)).mp (ht.trans ho.symm)
  exact wholePlane_missing_east_not_triangle W H hhit (uibhbotRootEdge W)
    C.root_missing_wholePlane N j hr




theorem uibhbotCodeLawRel_ae_dart_outer_or_triangle :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (_hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (_C : UIBHBOTCertifiedRootCapture W 0),
        ∀ d : WholePlaneDart W,
          Xor ((wholePlaneFaceSucc W H).SameCycle (uibhbotWholePlaneOuterDart W) d)
            (∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
              d ∈ wholePlaneDartι W N ''
                {a | a ∈ stageTriangleDartList (shiftedStream W N) j}) := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses,
    uibhbotCodeLawRel_ae_vertical_nonrecord] with W hW hhit hback
  obtain ⟨H, hcap, _⟩ := hW
  obtain ⟨C⟩ := hcap 0
  refine ⟨H, hhit, C, ?_⟩
  intro d
  have hexcl : (∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
      d ∈ wholePlaneDartι W N ''
        {a | a ∈ stageTriangleDartList (shiftedStream W N) j}) →
      ¬ (wholePlaneFaceSucc W H).SameCycle (uibhbotWholePlaneOuterDart W) d := by
    rintro ⟨N, j, hj⟩
    exact wholePlane_stageTriangle_not_outer W H hhit C N j d hj
  rcases d with ⟨e, b⟩
  cases b with
  | false => exact Or.inr ⟨west_dart_triangle W H hhit e,
      hexcl (west_dart_triangle W H hhit e)⟩
  | true =>
    by_cases hp : wholePlaneEdgePresent W e
    · have ht := present_east_dart_triangle W H hhit hback e hp
      exact Or.inr ⟨ht, hexcl ht⟩
    · have ho := wholePlane_missing_east_sameCycle W H hhit (uibhbotRootEdge W) e
        C.root_missing_wholePlane hp
      exact Or.inl ⟨ho, fun ht => hexcl ht ho⟩



theorem wholePlane_stageTriangle_faceOrbit_darts (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (j : TriangleCreationTime (shiftedStream W N)) :
    {d : WholePlaneDart W | (Quotient.mk _ d : FaceOrbit W H) =
        Quotient.mk _ (wholePlaneDartι W N
          (stageTriangleDartTriple (shiftedStream W N) j).1)} =
      wholePlaneDartι W N '' {a | a ∈ stageTriangleDartList (shiftedStream W N) j} := by
  ext d
  constructor
  · intro hd
    exact (wholePlane_stageTriangle_sameCycle_iff W H N j d).mp
      (Quotient.exact hd.symm)
  · intro hd
    exact Quotient.sound ((wholePlane_stageTriangle_sameCycle_iff W H N j d).mpr hd).symm





theorem uibhbotCodeLawRel_ae_faceOrbit_triangle :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (_hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (_C : UIBHBOTCertifiedRootCapture W 0),
        ∀ q : FaceOrbit W H,
          q ≠ (Quotient.mk _ (uibhbotWholePlaneOuterDart W) : FaceOrbit W H) ↔
            ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
              {d : WholePlaneDart W | (Quotient.mk _ d : FaceOrbit W H) = q} =
                wholePlaneDartι W N ''
                  {a | a ∈ stageTriangleDartList (shiftedStream W N) j} ∧
              ((stageTriangleDartList (shiftedStream W N) j).toFinset.image
                (wholePlaneDartι W N)).card = 3 := by
  filter_upwards [uibhbotCodeLawRel_ae_dart_outer_or_triangle] with W hW
  obtain ⟨H, hhit, C, hcover⟩ := hW
  refine ⟨H, hhit, C, fun q => ?_⟩
  constructor
  · intro hq
    obtain ⟨d, rfl⟩ := Quotient.exists_rep q
    rcases hcover d with ⟨ho, _⟩ | ⟨⟨N, j, hd⟩, _⟩
    · exact (hq (Quotient.sound ho.symm)).elim
    · have hclass : (Quotient.mk _ d : FaceOrbit W H) =
          Quotient.mk _ (wholePlaneDartι W N
            (stageTriangleDartTriple (shiftedStream W N) j).1) :=
        Quotient.sound ((wholePlane_stageTriangle_sameCycle_iff W H N j d).mpr hd).symm
      refine ⟨N, j, ?_, wholePlane_stageTriangle_darts_card W N j⟩
      rw [hclass]
      exact wholePlane_stageTriangle_faceOrbit_darts W H N j
  · rintro ⟨N, j, heq, _⟩ hq
    have hroot : uibhbotWholePlaneOuterDart W ∈
        wholePlaneDartι W N '' {a | a ∈ stageTriangleDartList (shiftedStream W N) j} := by
      rw [← heq]
      exact hq.symm
    exact wholePlane_missing_east_not_triangle W H hhit (uibhbotRootEdge W)
      C.root_missing_wholePlane N j hroot




theorem uibhbotCodeLawRel_ae_outerOrbit_missing_east :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W, ∀ d : WholePlaneDart W,
        (wholePlaneFaceSucc W H).SameCycle (uibhbotWholePlaneOuterDart W) d ↔
          d.2 = true ∧ ¬ wholePlaneEdgePresent W d.1 := by
  filter_upwards [uibhbotCodeLawRel_ae_dart_outer_or_triangle,
    uibhbotCodeLawRel_ae_vertical_nonrecord] with W hW hback
  obtain ⟨H, hhit, C, hcover⟩ := hW
  refine ⟨H, ?_⟩
  rintro ⟨e, b⟩
  constructor
  · intro ho
    have hnot : ¬ ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
        (e, b) ∈ wholePlaneDartι W N ''
          {a | a ∈ stageTriangleDartList (shiftedStream W N) j} := by
      rcases hcover (e, b) with ⟨_, hnot⟩ | ⟨_, hnot⟩
      · exact hnot
      · exact (hnot ho).elim
    cases b with
    | false => exact (hnot (west_dart_triangle W H hhit e)).elim
    | true =>
      refine ⟨rfl, fun hp => ?_⟩
      exact hnot (present_east_dart_triangle W H hhit hback e hp)
  · rintro ⟨hb, hm⟩
    cases b with
    | false => cases hb
    | true =>
      exact wholePlane_missing_east_sameCycle W H hhit (uibhbotRootEdge W) e
        C.root_missing_wholePlane hm






theorem uibhbotCodeLawRel_ae_outerOrbit_eq_chain :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W) (e : ℤ → WholePlaneEdge W),
        (∀ f : WholePlaneEdge W,
          ¬ wholePlaneEdgePresent W f ↔ ∃! k : ℤ, f = e k) ∧
        ∀ d : WholePlaneDart W,
          (wholePlaneFaceSucc W H).SameCycle (uibhbotWholePlaneOuterDart W) d ↔
            ∃! k : ℤ, d = (e k, true) := by
  filter_upwards [uibhbotCodeLawRel_ae_outerOrbit_missing_east,
    uibhbotCodeLawRel_ae_missing_edges_eq_range] with W hW hchain
  obtain ⟨H, houter⟩ := hW
  obtain ⟨e, he⟩ := hchain
  refine ⟨H, e, he, fun d => ?_⟩
  rw [houter d]
  constructor
  · rintro ⟨hb, hm⟩
    obtain ⟨k, hk, huniq⟩ := (he d.1).mp hm
    refine ⟨k, Prod.ext hk hb, fun l hl => huniq l (congrArg Prod.fst hl)⟩
  · rintro ⟨k, hk, huniq⟩
    refine ⟨congrArg Prod.snd hk, (he d.1).mpr ⟨k, congrArg Prod.fst hk, ?_⟩⟩
    intro l hl
    have hb : d.2 = true := congrArg (fun a : WholePlaneDart W => a.2) hk
    exact huniq l (Prod.ext hl hb)

end DirectedDistances.PaperProofs.Section5
