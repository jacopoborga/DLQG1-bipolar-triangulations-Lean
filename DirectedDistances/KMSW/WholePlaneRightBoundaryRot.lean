module

public import DirectedDistances.KMSW.WholePlaneRightBoundary
public import DirectedDistances.KMSW.RightBoundaryRightmost

/- probability-one scope: stated under an explicit rotation hypothesis / a.s.); not the paper result.
conditional reductions. It is not included in WholePlaneRotationHypothesis. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk
open scoped Classical

private def runBase (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private def ambientBase (W : ℤ → Fin 3) (d : WholePlaneDart W) : WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1

private theorem base_ι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    ambientBase W (wholePlaneDartι W N d) =
      wholePlaneVertexι W N (runBase (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [ambientBase, runBase, wholePlaneDartι, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeWest_ι W N d.1
  · exact wholePlaneEdgeEast_ι W N d.1

private theorem symm_base (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) :
    runBase w ((kmswInfRot w hfin).symm d) = runBase w d := by
  obtain ⟨n, hn⟩ := kmswInfRot_symm_eventually_eq_stage w hfin d
  obtain ⟨hd, he⟩ := hn n le_rfl
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  have hb (z : StageDart (kmswStage w n).nextEdge) :
      stageEndpoint (kmswStage w n) z = runBase w (z.1.val, z.2) := by
    obtain ⟨hw, he⟩ := edge_endpoints_eq w z.1.isLt
    cases hs : z.2 <;> simp only [stageEndpoint, runBase, hs,
      Bool.false_eq_true, ↓reduceIte, hw, he]
  have hr := ((stageRot_sameCycle_iff_endpoint_eq w n
    ((stageRot w n).symm x) x).mp
      ⟨1, (stageRot w n).apply_symm_apply x⟩)
  rw [he, ← hb ((stageRot w n).symm x), ← hb x]
  exact hr

private theorem symm_pow_base (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    runBase w (((kmswInfRot w hfin).symm ^ k) d) = runBase w d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, symm_base, ih]

private theorem symm_pow_fresh (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (N : ℕ) (d : ℕ × Bool)
    (hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (runBase (shiftedStream W N) d)) (k : ℕ) :
    ((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N d) =
      wholePlaneDartι W N (((kmswInfRot (shiftedStream W N) (H.1 N)).symm ^ k) d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let σ := (kmswInfRot (shiftedStream W N) (H.1 N)).symm
    let τ := (wholePlaneRotation W H).symm
    have hf' : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
        (runBase (shiftedStream W N) ((σ ^ k) d)) := by
      intro M hNM
      rw [symm_pow_base]
      exact hf M hNM
    let I : (ℕ × Bool) → WholePlaneDart W := wholePlaneDartι W N
    change (τ ^ (k + 1)) (I d) = I ((σ ^ (k + 1)) d)
    change (τ ^ k) (I d) = I ((σ ^ k) d) at ih
    have hstep : τ (I ((σ ^ k) d)) = I (σ ((σ ^ k) d)) :=
      wholePlaneRotation_symm_ι_of_fresh W H N ((σ ^ k) d) hf'
    calc
      (τ ^ (k + 1)) (I d) = τ ((τ ^ k) (I d)) :=
        Equiv.congr_fun (pow_succ' τ k) (I d)
      _ = τ (I ((σ ^ k) d)) := congrArg τ ih
      _ = I (σ ((σ ^ k) d)) := hstep
      _ = I ((σ ^ (k + 1)) d) :=
        congrArg I (Equiv.congr_fun (pow_succ' σ k) d).symm

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s.); not the paper result. One cofinally fresh representative computes every
inverse power, with the representative chosen before the power. -/
theorem wholePlaneRotation_symm_pow_at_common_run (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) :
    ∃ M, ∃ hNM : N ≤ M, ∀ k : ℕ,
      ((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N d) =
        wholePlaneDartι W M (((kmswInfRot (shiftedStream W M) (H.1 M)).symm ^ k)
          (wholePlaneDartTrans W N M hNM d)) := by
  obtain ⟨M, hNM, hf⟩ := H.2 N (runBase (shiftedStream W N) d)
  refine ⟨M, hNM, fun k => ?_⟩
  rw [← congrFun (wholePlaneDartι_trans W N M hNM) d]
  apply symm_pow_fresh
  intro L hML
  have hb : runBase (shiftedStream W M) (wholePlaneDartTrans W N M hNM d) =
      wholePlaneVertexTrans W N M hNM (runBase (shiftedStream W N) d) := by
    cases hs : d.2 <;> simp only [runBase, wholePlaneDartTrans, hs,
      Bool.false_eq_true, ↓reduceIte]
    · exact wholePlaneEdgeTrans_west W N M hNM d.1
    · exact wholePlaneEdgeTrans_east W N M hNM d.1
  rw [hb]
  exact hf L hML

private theorem dart_ι_injective (W : ℤ → Fin 3) (N : ℕ) :
    Function.Injective (wholePlaneDartι W N) := by
  intro d e he
  have hb : d.2 = e.2 := congrArg (fun x : WholePlaneEdge W × Bool => x.2) he
  have hf := congrArg (fun x : WholePlaneEdge W × Bool => x.1) he
  exact Prod.ext (wholePlaneEdgeι_injective W N hf) hb

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s.); not the paper result. Reduction of the colimit first-return comparison to
the corresponding cross-run comparisons. The input includes the gap condition;
this theorem does not prove that input at the shared root-terminal vertex. -/
theorem wholePlaneRotation_symm_firstReturn_of_cross_run
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool)
    (hind : ∀ M (hNM : N ≤ M), ∃ k : ℕ, 0 < k ∧
      (((kmswInfRot (shiftedStream W M) (H.1 M)).symm ^ k)
        (wholePlaneDartTrans W N M hNM d)) =
          wholePlaneDartTrans W N M hNM
            ((kmswInfRot (shiftedStream W N) (H.1 N)).symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (((kmswInfRot (shiftedStream W M) (H.1 M)).symm ^ j)
          (wholePlaneDartTrans W N M hNM d)) ∉
            Set.range (wholePlaneDartTrans W N M hNM)) :
    ∃ k : ℕ, 0 < k ∧
      ((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N d) =
        wholePlaneDartι W N ((kmswInfRot (shiftedStream W N) (H.1 N)).symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((wholePlaneRotation W H).symm ^ j) (wholePlaneDartι W N d) ∉
          Set.range (wholePlaneDartι W N) := by
  obtain ⟨M, hNM, hpow⟩ := wholePlaneRotation_symm_pow_at_common_run W H N d
  obtain ⟨k, hk, hret, hgap⟩ := hind M hNM
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hpow, hret]
    exact congrFun (wholePlaneDartι_trans W N M hNM) _
  · intro j hj hjk hmem
    obtain ⟨e, he⟩ := hmem
    apply hgap j hj hjk
    refine ⟨e, dart_ι_injective W M ?_⟩
    exact (congrFun (wholePlaneDartι_trans W N M hNM) e).trans (he.trans (hpow j))

private theorem trans_present (W : ℤ → Fin 3) (N M : ℕ) (hNM : N ≤ M)
    (e : ℕ) (hp : EdgePresent (shiftedStream W N) e) :
    EdgePresent (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e) := by
  obtain ⟨n, he, hp⟩ := hp
  let s := M - N
  have he' : e < (kmswStage (fun i => shiftedStream W M (s + i)) n).nextEdge := by
    simpa only [s, shiftedStream_shift W N M hNM] using he
  have hp' : (kmswStage (fun i => shiftedStream W M (s + i)) n).present e = true := by
    simpa only [s, shiftedStream_shift W N M hNM] using hp
  have hrel := kmswWindowPatchData_rel (shiftedStream W M) s n
  have hb := hrel.edge_bound e he'
  have ht := hrel.present e he' hp'
  have hmap := kmswWindowEdgeMapInf_eq_stage (shiftedStream W M) s n e he'
  refine ⟨s + n, ?_, ?_⟩
  · change kmswWindowEdgeMapInf (shiftedStream W M) s e < _
    rw [hmap]
    exact hb
  · change (kmswStage (shiftedStream W M) (s + n)).present
      (kmswWindowEdgeMapInf (shiftedStream W M) s e) = true
    rw [hmap]
    exact ht

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s.); not the paper result. Run-present edges remain present in the colimit;
no converse for missing run edges is asserted. -/
theorem wholePlaneEdgePresent_ι_of_run_present (W : ℤ → Fin 3) (N e : ℕ)
    (hp : EdgePresent (shiftedStream W N) e) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N e) := by
  apply (wholePlaneEdgePresent_ι W N e).mpr
  exact ⟨N, le_rfl, fun M hNM => trans_present W N M hNM e hp⟩

private theorem ambient_symm_pow_base (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) (k : ℕ) :
    ambientBase W (((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N d)) =
      ambientBase W (wholePlaneDartι W N d) := by
  obtain ⟨M, hNM, hpow⟩ := wholePlaneRotation_symm_pow_at_common_run W H N d
  rw [hpow k, base_ι, symm_pow_base, ← base_ι]
  exact congrArg (ambientBase W) (congrFun (wholePlaneDartι_trans W N M hNM) d)

private theorem rightmost_of_firstReturn (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N e g : ℕ)
    (hp : EdgePresent (shiftedStream W N) e)
    (hw : edgeWest (shiftedStream W N) e = 1)
    (hg : EdgePresent (shiftedStream W N) g)
    (hret : ∃ k : ℕ, 0 < k ∧
      ((wholePlaneRotation W H).symm ^ k) (wholePlaneDartι W N (e, false)) =
        wholePlaneDartι W N (g, true) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((wholePlaneRotation W H).symm ^ j) (wholePlaneDartι W N (e, false)) ∉
          Set.range (wholePlaneDartι W N)) :
    wholePlaneRightmostOutgoingAt W H (wholePlaneVertexι W N 1)
      (wholePlaneEdgeι W N e) := by
  classical
  obtain ⟨k, hk, hret, hgap⟩ := hret
  let Q := fun j : ℕ => 0 < j ∧ wholePlaneEdgePresent W
    (((wholePlaneRotation W H).symm ^ j) (wholePlaneDartι W N (e, false))).1
  have hex : ∃ j, Q j := ⟨k, hk, by
    rw [hret]
    exact wholePlaneEdgePresent_ι_of_run_present W N g hg⟩
  let m := Nat.find hex
  have hm : Q m := Nat.find_spec hex
  have hmk : m ≤ k := Nat.find_min' hex (by
    exact ⟨hk, by rw [hret]; exact wholePlaneEdgePresent_ι_of_run_present W N g hg⟩)
  have hside : (((wholePlaneRotation W H).symm ^ m)
      (wholePlaneDartι W N (e, false))).2 = true := by
    by_cases hme : m = k
    · rw [hme, hret]
      rfl
    · let z := ((wholePlaneRotation W H).symm ^ m) (wholePlaneDartι W N (e, false))
      have hb := ambient_symm_pow_base W H N (e, false) m
      have hzw : z.2 = false → wholePlaneEdgeWest W z.1 = wholePlaneVertexι W N 1 := by
        intro hz
        change ambientBase W z = _ at hb
        simpa only [ambientBase, hz, wholePlaneDartι, Bool.false_eq_true,
          ↓reduceIte, wholePlaneEdgeWest_ι, hw] using hb
      cases hs : z.2 with
      | true => rfl
      | false =>
        obtain ⟨f, _, _, hf⟩ := wholePlane_root_terminal_outgoing_lift W H N z.1
          hm.2 (hzw hs)
        apply False.elim
        apply hgap m hm.1 (by omega)
        exact ⟨(f, false), Prod.ext hf hs.symm⟩
  refine ⟨wholePlaneEdgePresent_ι_of_run_present W N e hp, ?_, m, hm.1, hside, hm.2, ?_⟩
  · rw [wholePlaneEdgeWest_ι, hw]
  · intro j hj hjm hpj
    exact Nat.find_min hex hjm ⟨hj, hpj⟩

private theorem ae_run_hits :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      BoundaryHitWitnesses (shiftedStream W N) := by
  apply ae_all_iff.2
  intro N
  have hf := iidCodes_ae_boundaryHitWitnesses
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath N] at hf
  have hp := ae_of_ae_map (measurable_shiftedCodePath N).aemeasurable hf
  simpa [shiftedCodePath, insertDummy] using hp

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s.); not the paper result. Conditional simultaneous all-run rightmostness.
The displayed cross-run inverse first-return invariant remains an obligation.
The coordinate hits used in the proof are supplied by the iid law, not by H. -/
theorem wholePlaneIID_ae_rightmost_of_cross_run_induced_rotation :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∃ H : WholePlaneRotationHypothesis W,
      (∀ (N M : ℕ) (hNM : N ≤ M) (d : ℕ × Bool),
        (if d.2 then edgeEast (shiftedStream W N) d.1
          else edgeWest (shiftedStream W N) d.1) = 1 →
        ∃ k : ℕ, 0 < k ∧
          (((kmswInfRot (shiftedStream W M) (H.1 M)).symm ^ k)
            (wholePlaneDartTrans W N M hNM d)) =
              wholePlaneDartTrans W N M hNM
                ((kmswInfRot (shiftedStream W N) (H.1 N)).symm d) ∧
          ∀ j : ℕ, 0 < j → j < k →
            (((kmswInfRot (shiftedStream W M) (H.1 M)).symm ^ j)
              (wholePlaneDartTrans W N M hNM d)) ∉
                Set.range (wholePlaneDartTrans W N M hNM)) →
      ∀ N : ℕ, wholePlaneRightmostOutgoingAt W H (wholePlaneVertexι W N 1)
        (wholePlaneEdgeι W N (kmswRightBoundaryEdge (shiftedStream W N) 1)) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis, ae_run_hits] with W H hh
  refine ⟨H, ?_⟩
  intro hind N
  let w := shiftedStream W N
  have hp := boundaryVertex_right_edge_present_source w (hh N) (k := 1) le_rfl
  have hw : edgeWest w (kmswRightBoundaryEdge w 1) = 1 := by
    exact hp.2.1.trans (boundaryVertex_one w (hh N))
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := (hh N).rightHit (max 1 (-a)) (le_max_left _ _)
    change R w n = -max 1 (-a) at hn
    have hm : -a ≤ max (1 : ℤ) (-a) := le_max_right _ _
    exact ⟨n, by omega⟩
  have hface := kmswInfFaceSucc_right_of_unbounded_below w (H.1 N) hR 0
  have hpred : (kmswInfRot w (H.1 N)).symm (kmswRightBoundaryEdge w 1, false) =
      (0, true) := by
    change (kmswInfRot w (H.1 N)).symm
      (kmswRightBoundaryEdge w (0 + 1), false) = (kmswRightBoundaryEdge w 0, true) at hface
    simpa only [zero_add, kmswRightBoundaryEdge_zero] using hface
  have hroot : EdgePresent w 0 := ⟨0, by change 0 < 1; omega, rfl⟩
  apply rightmost_of_firstReturn W H N (kmswRightBoundaryEdge w 1) 0 hp.1 hw hroot
  have hr := wholePlaneRotation_symm_firstReturn_of_cross_run W H N
    (kmswRightBoundaryEdge w 1, false) (fun M hNM =>
      hind N M hNM _ (by exact hw))
  obtain ⟨k, hk, hreturn, hgap⟩ := hr
  exact ⟨k, hk, hreturn.trans (congrArg (wholePlaneDartι W N) hpred), hgap⟩

end DirectedDistances.KMSW
