module

public import DirectedDistances.KMSW.KMSWInverseStepLink
public import DirectedDistances.KMSW.StageIncidenceChains
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Stage frontier chain obstruction

The initial single edge occurs in both the `UL` and `LR` runs of
pairwise-disjointness condition on all four edge-ID lists cannot hold at every
stage. The source uses oriented darts when distinguishing the two sides of
this root edge. -/

public section
namespace DirectedDistances.KMSW

/-- Stage-frontier chain bookkeeping for the edge-ID runs in `def-kmsw`
boundary, status, and record invariants as a helper toward thm-kmsw
the paper result. The lower-left edge incidence is with the west endpoint of
the first UL edge, and missing edges are disjoint from the present UL and LR
runs. -/
structure KMSWStageFrontierChain (u : ℕ → Fin 3) (m : ℕ) : Prop where
  /-- The head of UR starts at the terminal endpoint of the active edge. -/
  UR_head_incidence : ∀ e es, (kmswStage u m).UR = e :: es →
    (kmswStage u m).west e = (kmswStage u m).east (kmswStage u m).active
  /-- The upper-right run is chained east-to-west. -/
  UR_chain : List.IsChain
    (fun e f => (kmswStage u m).west f = (kmswStage u m).east e)
    (kmswStage u m).UR
  /-- Every upper-right edge is allocated and missing. -/
  UR_missing_bounded : ∀ e ∈ (kmswStage u m).UR,
    (kmswStage u m).present e = false ∧ e < (kmswStage u m).nextEdge
  /-- The upper-right edge IDs do not repeat. -/
  UR_nodup : (kmswStage u m).UR.Nodup
  /-- UL is nonempty and ends at the active edge. -/
  UL_nonempty_active_last : (kmswStage u m).UL ≠ [] ∧
    (kmswStage u m).UL.getLast? = some (kmswStage u m).active
  /-- The nearest UL predecessor meets the active edge at its west endpoint. -/
  UL_predecessor_incidence : ∀ e es,
    (kmswStage u m).UL.dropLast.reverse = e :: es →
    (kmswStage u m).east e = (kmswStage u m).west (kmswStage u m).active
  /-- The upper-left run is chained east-to-west. -/
  UL_chain : List.IsChain
    (fun e f => (kmswStage u m).east e = (kmswStage u m).west f)
    (kmswStage u m).UL
  /-- Every upper-left edge is present. -/
  UL_present : ∀ e ∈ (kmswStage u m).UL, (kmswStage u m).present e = true
  /-- The upper-left edge IDs do not repeat. -/
  UL_nodup : (kmswStage u m).UL.Nodup
  /-- The head of LL shares the west side of the first UL edge. -/
  LL_head_incidence : ∀ e es, (kmswStage u m).LL = e :: es →
    (kmswStage u m).west e =
      (kmswStage u m).west ((kmswStage u m).UL.head
        (kmswStage_UL_nonempty_active_last u m).1)
  /-- The lower-left run is chained east-to-west. -/
  LL_chain : List.IsChain
    (fun e f => (kmswStage u m).east e = (kmswStage u m).west f)
    (kmswStage u m).LL
  /-- Every lower-left edge is allocated and missing. -/
  LL_missing_bounded : ∀ e ∈ (kmswStage u m).LL,
    (kmswStage u m).present e = false ∧ e < (kmswStage u m).nextEdge
  /-- The lower-left edge IDs do not repeat. -/
  LL_nodup : (kmswStage u m).LL.Nodup
  /-- Every lower-right edge is present. -/
  LR_present : ∀ e ∈ (kmswStage u m).LR, (kmswStage u m).present e = true
  /-- Missing boundary IDs are disjoint from the present UL and LR IDs. -/
  missing_present_disjoint : List.Disjoint
    ((kmswStage u m).UR ++ (kmswStage u m).LL)
    ((kmswStage u m).UL ++ (kmswStage u m).LR)
  /-- The two missing boundary runs have no edge ID in common. -/
  UR_LL_disjoint : List.Disjoint (kmswStage u m).UR (kmswStage u m).LL
  /-- Every allocated missing edge occurs in UR or LL. -/
  missing_edge_cover : ∀ e, e < (kmswStage u m).nextEdge →
    (kmswStage u m).present e = false →
      e ∈ (kmswStage u m).UR ∨ e ∈ (kmswStage u m).LL

/-- Every finite KMSW stage satisfies the bundled stage-frontier chain
invariants. The component proofs reuse the established induction over the
activation, pendant, left-existing, left-fresh, and up updates in the ordered
boundary and status results (`def-kmsw`,
the paper result. -/
theorem kmswStageFrontierChain_all (u : ℕ → Fin 3) :
    ∀ m, KMSWStageFrontierChain u m := by
  intro m
  let s := kmswStage u m
  have hstatus := kmswStage_status u m
  have hids := kmswStage_boundary_ids_lt_nextEdge u m
  have hboundary := kmswStage_boundary_chain_invariant u m
  have hlast := kmswStage_UL_nonempty_active_last u m
  have hULnd : s.UL.Nodup := by
    rw [kmswStage_UL_eq]
    exact (List.Nodup.filter _ List.nodup_range).map
      (CutConverse.act_injective u)
  refine ⟨?_, ?_, ?_, hstatus.2.2.2.1, hlast, ?_, ?_, hstatus.2.1,
    hULnd, ?_, ?_, ?_, hstatus.2.2.2.2.1, hstatus.2.2.1,
    ?_, ?_, ?_⟩
  · intro e es he
    exact hboundary.2.2.2.2.2.1 e es he
  · have hUR : List.IsChain (fun e f => s.east e = s.west f) s.UR :=
      (show List.IsChain (fun e f => s.east e = s.west f)
        (s.UL ++ s.UR) from hboundary.1).right_of_append
    exact hUR.imp (fun e f h => h.symm)
  · intro e he
    have hb : e < s.nextEdge := hids.2 e (by
      simp only [List.mem_append]
      tauto)
    exact ⟨(hstatus.1 e hb).2 (Or.inl he), hb⟩
  · intro e es he
    have hULlast := kmswStage_UL_last u m
    obtain ⟨xs, hxs⟩ := hULlast
    have hxsS : s.UL = xs ++ [s.active] := by simpa [s] using hxs
    have hxsDrop : xs = s.UL.dropLast := by rw [hxsS]; simp
    have hrev : s.UL.reverse = s.active :: e :: es := by
      calc
        s.UL.reverse = (xs ++ [s.active]).reverse := congrArg List.reverse hxsS
        _ = s.active :: xs.reverse := by simp
        _ = s.active :: e :: es := by rw [hxsDrop, he]
    have hcoherent := CutConverse.ul_coherent u m
    change s.UL.reverse.map s.east =
      s.east s.active :: (s.UL.reverse.map s.west).dropLast at hcoherent
    rw [hrev] at hcoherent
    simp only [List.map_cons, List.dropLast_cons_cons] at hcoherent
    exact (List.cons.inj (List.cons.inj hcoherent).2).1
  · change List.IsChain (fun e f => s.east e = s.west f) s.UL
    exact (show List.IsChain (fun e f => s.east e = s.west f)
      (s.UL ++ s.UR) from hboundary.1).left_of_append
  · intro e es he
    have hstart := hboundary.2.2.1
    have hULne : s.UL ≠ [] := hlast.1
    have hLLne : s.LL ≠ [] := by rw [he]; simp
    have hupper : boundaryStart s (s.UL ++ s.UR) =
        some (s.west (s.UL.head hULne)) := by
      unfold boundaryStart
      rw [List.head?_append_of_ne_nil _ hULne,
        List.head?_eq_some_head hULne]
      simp
    have hlower : boundaryStart s (s.LL ++ s.LR) =
        some (s.west e) := by
      unfold boundaryStart
      rw [List.head?_append_of_ne_nil _ hLLne, he]
      simp
    have hEq := hstart.trans hlower
    rw [hupper] at hEq
    exact (Option.some.inj hEq).symm
  · change List.IsChain (fun e f => s.east e = s.west f) s.LL
    exact (show List.IsChain (fun e f => s.east e = s.west f)
      (s.LL ++ s.LR) from hboundary.2.1).left_of_append
  · intro e he
    have hb : e < s.nextEdge := hids.2 e (by
      simp only [List.mem_append]
      tauto)
    exact ⟨(hstatus.1 e hb).2 (Or.inr he), hb⟩
  · apply List.disjoint_left.mpr
    intro e heMissing hePresent
    simp only [List.mem_append] at heMissing hePresent
    rcases heMissing with heUR | heLL <;>
      rcases hePresent with heUL | heLR
    · have hb : e < s.nextEdge := hids.2 e (by
        simp only [List.mem_append]
        tauto)
      have hmiss : s.present e = false := (hstatus.1 e hb).2 (Or.inl heUR)
      have hpresent := hstatus.2.1 e heUL
      rw [hmiss] at hpresent
      cases hpresent
    · have hb : e < s.nextEdge := hids.2 e (by
        simp only [List.mem_append]
        tauto)
      have hmiss : s.present e = false := (hstatus.1 e hb).2 (Or.inl heUR)
      have hpresent := hstatus.2.2.1 e heLR
      rw [hmiss] at hpresent
      cases hpresent
    · have hb : e < s.nextEdge := hids.2 e (by
        simp only [List.mem_append]
        tauto)
      have hmiss : s.present e = false := (hstatus.1 e hb).2 (Or.inr heLL)
      have hpresent := hstatus.2.1 e heUL
      rw [hmiss] at hpresent
      cases hpresent
    · have hb : e < s.nextEdge := hids.2 e (by
        simp only [List.mem_append]
        tauto)
      have hmiss : s.present e = false := (hstatus.1 e hb).2 (Or.inr heLL)
      have hpresent := hstatus.2.2.1 e heLR
      rw [hmiss] at hpresent
      cases hpresent
  · apply List.disjoint_left.mpr
    intro e heUR heLL
    exact hstatus.2.2.2.2.2 e heUR heLL
  · intro e he hmissing
    exact (hstatus.1 e he).mp hmissing

/-- shows that `UL` and `LR` are not disjoint as edge-ID lists. -/
theorem kmswStage_initial_UL_LR_not_disjoint (u : ℕ → Fin 3) :
    ¬ List.Disjoint (kmswStage u 0).UL (kmswStage u 0).LR := by
  intro hdisjoint
  have hUL : 0 ∈ (kmswStage u 0).UL := by simp [kmswStage, kmswInit]
  have hLR : 0 ∈ (kmswStage u 0).LR := by simp [kmswStage, kmswInit]
  exact (List.disjoint_left.mp hdisjoint) hUL hLR

end DirectedDistances.KMSW
