module

public import DirectedDistances.KMSW.KMSWWholePlaneFaces
public import DirectedDistances.KMSW.WholePlaneRotationAE
import DirectedDistances.KMSW.OutgoingIntervalFreshLeft

/-! probability-one scope: stated under an explicit rotation hypothesis / a.s., not for every walk);
not the paper result.

The colimit corner below uses the rotation on geometric darts, skipping missing edges.
The finite prefix exclusion is an actual KMSW frontier invariant. It does not identify
the run boundary with an ambient extremal path or establish an outgoing interval. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s., not for every walk); not the paper result.
An outgoing corner is rightmost when the first present dart encountered by inverse
rotation is incoming. Missing geometric darts are skipped and receive no orientation.
Existence, uniqueness and the boundary identification are not asserted. -/
@[expose] def wholePlaneRightmostOutgoingAt (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    (e : WholePlaneEdge W) : Prop :=
  wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v ∧
    ∃ k : ℕ, 0 < k ∧
      (((wholePlaneRotation W H).symm ^ k) (e, false)).2 = true ∧
      wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ k) (e, false)).1 ∧
      ∀ j : ℕ, 0 < j → j < k →
        ¬ wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ j) (e, false)).1

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s., not for every walk); not the paper result.
This finite transition identity identifies the terminal endpoint of the window root. -/
theorem wholePlaneVertexTrans_root_terminal (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) :
    wholePlaneVertexTrans W N M h 1 =
      (kmswStage (shiftedStream W M) (M - N)).east
        (kmswStage (shiftedStream W M) (M - N)).active := by
  unfold wholePlaneVertexTrans
  rw [kmswWindowVertexMapInf_eq_stage (shiftedStream W M) (M - N) 0 1
    (by change 1 < 2; omega)]
  rfl

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s., not for every walk); not the paper result.
An edge already present in the prefix before the window starts cannot leave the
a claim about the order of edges that become present later. -/
theorem wholePlane_prefix_present_not_outgoing_root_terminal
    (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (f : ℕ)
    (hf : f < (kmswStage (shiftedStream W M) (M - N)).nextEdge)
    (hp : (kmswStage (shiftedStream W M) (M - N)).present f = true) :
    wholePlaneEdgeWest W (wholePlaneEdgeι W M f) ≠ wholePlaneVertexι W N 1 := by
  have hfront := stageOutgoing_active_east_empty (shiftedStream W M) (M - N)
    (⟨⟨f, hf⟩, false⟩) ⟨rfl, hp⟩
  have hwest : edgeWest (shiftedStream W M) f ≠ wholePlaneVertexTrans W N M h 1 := by
    rw [wholePlaneVertexTrans_root_terminal]
    intro heq
    apply hfront
    change (kmswStage (shiftedStream W M) (M - N)).west f = _
    rw [(edge_endpoints_eq (shiftedStream W M) hf).1]
    exact heq
  intro heq
  apply hwest
  apply wholePlaneVertexι_injective W M
  rw [wholePlaneEdgeWest_ι] at heq
  exact heq.trans (congrFun (wholePlaneVertexι_trans W N M h) 1).symm

private theorem active_present (w : ℕ → Fin 3) (m : ℕ) :
    (kmswStage w m).present (act w m) = true := by
  apply (kmswStage_status w m).2.1
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
  rw [hxs]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private theorem window_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem trans_act (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
    window_act (shiftedStream W M) (M - N) k

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s., not for every walk); not the paper result.
At the terminal vertex of the run root, every ambient present outgoing edge comes
from a present outgoing edge of that run. This includes prefix missing edges which
are activated later. It proves edge coverage, not their rotation order. -/
theorem wholePlane_root_terminal_outgoing_lift (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (e : WholePlaneEdge W)
    (hp : wholePlaneEdgePresent W e)
    (hw : wholePlaneEdgeWest W e = wholePlaneVertexι W N 1) :
    ∃ f : ℕ, EdgePresent (shiftedStream W N) f ∧
      edgeWest (shiftedStream W N) f = 1 ∧ wholePlaneEdgeι W N f = e := by
  obtain ⟨⟨K, g⟩, he⟩ := Quotient.exists_rep e
  change wholePlaneEdgeι W K g = e at he
  obtain ⟨A, hKA, hA⟩ := wholePlaneEdgePresent_eventually W H K g
  let M := max N A
  have hNM : N ≤ M := Nat.le_max_left _ _
  have hAM : A ≤ M := Nat.le_max_right _ _
  let f := wholePlaneEdgeTrans W K M (hKA.trans hAM) g
  have hfp : EdgePresent (shiftedStream W M) f :=
    (hA M hAM).mpr (he.symm ▸ hp)
  have hfι : wholePlaneEdgeι W M f = e :=
    (congrFun (wholePlaneEdgeι_trans W K M (hKA.trans hAM)) g).trans he
  have hfw : wholePlaneEdgeWest W (wholePlaneEdgeι W M f) =
      wholePlaneVertexι W N 1 := hfι ▸ hw
  obtain ⟨t, hft, hpt⟩ := hfp
  obtain ⟨m, _, hfm⟩ := stagePresent_exists_active (shiftedStream W M) t f hft hpt
  have hmb : f < (kmswStage (shiftedStream W M) m).nextEdge := by
    rw [hfm]
    exact act_lt_nextEdge _ le_rfl
  have hmp : (kmswStage (shiftedStream W M) m).present f = true := by
    rw [hfm]
    exact active_present _ _
  have hs : M - N ≤ m := by
    by_contra hn
    have hms : m ≤ M - N := by omega
    obtain ⟨hb, hpast⟩ := present_mono (shiftedStream W M) hmb hmp (M - N) hms
    exact wholePlane_prefix_present_not_outgoing_root_terminal W N M hNM f hb hpast hfw
  let q := act (shiftedStream W N) (m - (M - N))
  have hq : wholePlaneEdgeTrans W N M hNM q = f := by
    dsimp only [q]
    rw [trans_act, show M - N + (m - (M - N)) = m by omega]
    exact hfm.symm
  have hv : edgeWest (shiftedStream W M) f = wholePlaneVertexTrans W N M hNM 1 := by
    apply wholePlaneVertexι_injective W M
    rw [← wholePlaneEdgeWest_ι]
    exact hfw.trans (congrFun (wholePlaneVertexι_trans W N M hNM) 1).symm
  have hqw : edgeWest (shiftedStream W N) q = 1 := by
    apply wholePlaneVertexTrans_injective W N M hNM
    rw [← wholePlaneEdgeTrans_west, hq, hv]
  refine ⟨q, ⟨m - (M - N), act_lt_nextEdge _ le_rfl, active_present _ _⟩, hqw, ?_⟩
  calc
    wholePlaneEdgeι W N q =
        wholePlaneEdgeι W M (wholePlaneEdgeTrans W N M hNM q) :=
      (congrFun (wholePlaneEdgeι_trans W N M hNM) q).symm
    _ = e := by rw [hq]; exact hfι

/- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
a.s., not for every walk); not the paper result.
Simultaneous all-run outgoing-edge coverage at the root terminal vertices, almost -/
theorem wholePlaneIID_ae_root_terminal_outgoing_lift :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ (N : ℕ) (e : WholePlaneEdge W),
      wholePlaneEdgePresent W e →
      wholePlaneEdgeWest W e = wholePlaneVertexι W N 1 →
      ∃ f : ℕ, EdgePresent (shiftedStream W N) f ∧
        edgeWest (shiftedStream W N) f = 1 ∧ wholePlaneEdgeι W N f = e := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis] with W H
  exact wholePlane_root_terminal_outgoing_lift W H

end DirectedDistances.KMSW
