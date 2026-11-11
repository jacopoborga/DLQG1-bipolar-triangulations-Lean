/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBusemannIdentified
public import DirectedDistances.KMSW.WholePlaneRootedMapFields

/-! Helpers toward the exhaustive boundary description in Proposition 5.11 -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk



private theorem boundaryHitTime_eq_strictLeftRecord (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {m : ℕ} {q : ℤ}
    (hq : q ≤ -1) (hvalue : L w m = q)
    (hrecord : ∀ j < m, L w m < L w j) :
    boundaryHitTime w h q = m := by
  have hq0 : q ≠ 0 := by omega
  have hqpos : ¬ 0 < q := by omega
  have hle : boundaryHitTime w h q ≤ m := by
    unfold boundaryHitTime
    simp only [dite_eq_right hq0, dite_eq_right hqpos]
    exact Nat.find_min' (h.leftHit q hq) hvalue
  have hge : m ≤ boundaryHitTime w h q := by
    by_contra hnot
    have hlt : boundaryHitTime w h q < m := by omega
    have hfirst := boundaryHitTime_left_spec w h hq
    have hstrict := hrecord (boundaryHitTime w h q) hlt
    rw [hfirst, hvalue] at hstrict
    exact (lt_irrefl q) hstrict
  omega





theorem wholePlaneMissingRunEdge_firstHitLL (W : ℤ → Fin 3) (N e : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hm : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W N e)) :
    ∃ q : ℤ, q ≤ -1 ∧
      e = kmswLLCreatedEdge (shiftedStream W N)
        (boundaryHitTime (shiftedStream W N) h q) := by
  let w := shiftedStream W N
  have hm' : ¬ EdgePresent w e := by
    intro hp
    exact hm (wholePlaneEdgePresent_ι_of_run_present W N e hp)
  obtain ⟨n, hn⟩ := futureMap_missing_eventually_LL w h.R_unbounded_below e hm'
  obtain ⟨m, hmpos, _, hrecord, hedge⟩ :=
    kmswStage_LL_edge_created_at_record w n e (hn n le_rfl).2
  have hzero : L w 0 = 0 := by simp [L]
  have hnegative : L w m ≤ -1 := by
    have hs := hrecord 0 (by omega : 0 < m)
    rw [hzero] at hs
    omega
  refine ⟨L w m, hnegative, ?_⟩
  rw [boundaryHitTime_eq_strictLeftRecord w h hnegative rfl hrecord]
  exact hedge





theorem uibhbotCodeLawRel_ae_missing_edges_firstHitLL :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N),
        ∀ f : WholePlaneEdge W, ¬ wholePlaneEdgePresent W f →
          ∃ N e q, wholePlaneEdgeι W N e = f ∧ q ≤ -1 ∧
            e = kmswLLCreatedEdge (shiftedStream W N)
              (boundaryHitTime (shiftedStream W N) (hhit N) q) := by
  filter_upwards [uibhbotCodeLawRel_ae_boundaryHitWitnesses] with W hhit
  refine ⟨hhit, ?_⟩
  intro f hf
  obtain ⟨⟨N, e⟩, he⟩ := Quotient.exists_rep f
  change wholePlaneEdgeι W N e = f at he
  have hm : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W N e) := by
    rw [he]
    exact hf
  obtain ⟨q, hq, hfirst⟩ := wholePlaneMissingRunEdge_firstHitLL W N e (hhit N) hm
  exact ⟨N, e, q, he, hq, hfirst⟩

end DirectedDistances.PaperProofs.Section5
