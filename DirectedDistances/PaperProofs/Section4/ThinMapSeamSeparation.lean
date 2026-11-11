module

public import DirectedDistances.PaperProofs.Section4.ThinMapSideCarrier
import DirectedDistances.PlanarMap.PlanarPathCutHalves
import DirectedDistances.PlanarMap.PlanarPathCutLeftmostRegion

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/



















public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (P : InfinitePresentPath w ⟨0⟩) (B : ThinMapBoundaryRays w hfin)





theorem thinMapBoundary_faceSucc_mem_iff (d : ℕ × Bool) :
    kmswInfFaceSucc w hfin d ∈ Set.range B.left ∪ Set.range B.right ↔
      d ∈ Set.range B.left ∪ Set.range B.right := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · cases i with
      | zero =>
          have hd : d = B.right 0 :=
            (kmswInfFaceSucc w hfin).injective (hi.symm.trans B.junction.symm)
          exact Or.inr ⟨0, hd.symm⟩
      | succ i =>
          have hd : d = B.left i :=
            (kmswInfFaceSucc w hfin).injective (hi.symm.trans (B.left_step i).symm)
          exact Or.inl ⟨i, hd.symm⟩
    · have hd : d = B.right (i + 1) :=
        (kmswInfFaceSucc w hfin).injective (hi.symm.trans (B.right_step i).symm)
      exact Or.inr ⟨i + 1, hd.symm⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl ⟨i + 1, (B.left_step i).symm⟩
    · cases i with
      | zero => exact Or.inl ⟨0, B.junction.symm⟩
      | succ i => exact Or.inr ⟨i, (B.right_step i).symm⟩





theorem thinMapLeftBoundary_faceReach_not_mem_right {a d : ℕ × Bool}
    (ha : a ∈ Set.range B.left)
    (hreach : Relation.ReflTransGen (fun x y => y = kmswInfFaceSucc w hfin x) a d) :
    d ∉ Set.range B.right := by
  have hleft : d ∈ Set.range B.left := by
    induction hreach with
    | refl => exact ha
    | @tail b c _ hstep ih =>
        obtain ⟨i, rfl⟩ := ih
        exact ⟨i + 1, (B.left_step i).symm.trans hstep.symm⟩
  exact Set.disjoint_left.mp B.rays_disjoint hleft





theorem thinMapSideSeeds_inter_subset_seam :
    thinMapSideSeeds w hfin P B .left ∩ thinMapSideSeeds w hfin P B .right ⊆
      thinMapSeamDarts w P := by
  rintro d ⟨hleft, hright⟩
  rcases hleft with hleft | ⟨i, rfl⟩
  · rcases hright with hright | ⟨i, rfl⟩
    · exact (Set.disjoint_left.mp B.rays_disjoint hleft hright).elim
    · exact ⟨i, rfl⟩
  · exact ⟨i, rfl⟩






@[expose] def thinMapStageSideStep (side : ThinMapSide) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge) : Prop :=
  (e = (kmswMap w n).faceSucc d ∧
    ((d.1.val, d.2) ∉ Set.range B.left ∪ Set.range B.right ∨
      ((d.1.val, d.2) ∈ thinMapBoundaryArc w hfin B side ∧
        (e.1.val, e.2) ∈ thinMapBoundaryArc w hfin B side))) ∨
  (e = edgeFlip _ d ∧ (d.1.val, d.2) ∉ thinMapSeamDarts w P)

private theorem stageVal_injective (k : ℕ) :
    Function.Injective (fun d : StageDart k => (d.1.val, d.2)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  obtain ⟨he, hb⟩ := Prod.mk.inj h
  cases Fin.ext he
  cases hb
  rfl

private theorem sideStep_eventually_stage (side : ThinMapSide) {d e : ℕ × Bool}
    (hstep : thinMapSideStep w hfin P B side d e) :
    ∃ N, ∀ n ≥ N, ∃ hd : d.1 < (kmswStage w n).nextEdge,
      ∃ he : e.1 < (kmswStage w n).nextEdge,
        thinMapStageSideStep w hfin P B side n (⟨d.1, hd⟩, d.2) (⟨e.1, he⟩, e.2) := by
  rcases hstep with ⟨heq, hboundary⟩ | ⟨heq, hseam⟩
  · obtain ⟨N, hN⟩ := kmswInfFaceSucc_eventually_eq_stage w hfin d
    refine ⟨max N e.1, fun n hn => ?_⟩
    obtain ⟨hd, hface⟩ := hN n (le_trans (le_max_left _ _) hn)
    have he := kmsw_nextEdge_unbounded w e.1 n (le_trans (le_max_right _ _) hn)
    refine ⟨hd, he, Or.inl ⟨?_, hboundary⟩⟩
    apply stageVal_injective
    exact heq.trans hface
  · refine ⟨max d.1 e.1, fun n hn => ?_⟩
    have hd := kmsw_nextEdge_unbounded w d.1 n (le_trans (le_max_left _ _) hn)
    have he := kmsw_nextEdge_unbounded w e.1 n (le_trans (le_max_right _ _) hn)
    refine ⟨hd, he, Or.inr ⟨?_, hseam⟩⟩
    apply stageVal_injective
    exact heq






theorem thinMapSideReach_eventually_stage (side : ThinMapSide) {a d : ℕ × Bool}
    (hreach : Relation.ReflTransGen (thinMapSideStep w hfin P B side) a d) :
    ∃ N, ∀ n ≥ N, ∃ ha : a.1 < (kmswStage w n).nextEdge,
      ∃ hd : d.1 < (kmswStage w n).nextEdge,
        Relation.ReflTransGen (thinMapStageSideStep w hfin P B side n)
          (⟨a.1, ha⟩, a.2) (⟨d.1, hd⟩, d.2) := by
  induction hreach with
  | refl =>
      refine ⟨a.1, fun n hn => ?_⟩
      have ha := kmsw_nextEdge_unbounded w a.1 n hn
      exact ⟨ha, ha, Relation.ReflTransGen.refl⟩
  | @tail b c _ hstep ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨M, hM⟩ := sideStep_eventually_stage w hfin P B side hstep
      refine ⟨max N M, fun n hn => ?_⟩
      obtain ⟨ha, hb, hchain⟩ := hN n (le_trans (le_max_left _ _) hn)
      obtain ⟨_, hc, hlast⟩ := hM n (le_trans (le_max_right _ _) hn)
      exact ⟨ha, hc, Relation.ReflTransGen.tail hchain hlast⟩






theorem thinMapSideClosure_eventually_stage (side : ThinMapSide) {d : ℕ × Bool}
    (hd : d ∈ thinMapSideClosure w hfin P B side) :
    ∃ a ∈ thinMapSideSeeds w hfin P B side,
      ∃ N, ∀ n ≥ N, ∃ ha : a.1 < (kmswStage w n).nextEdge,
        ∃ hd : d.1 < (kmswStage w n).nextEdge,
          Relation.ReflTransGen (thinMapStageSideStep w hfin P B side n)
            (⟨a.1, ha⟩, a.2) (⟨d.1, hd⟩, d.2) := by
  obtain ⟨a, ha, hreach⟩ := hd
  exact ⟨a, ha, thinMapSideReach_eventually_stage w hfin P B side hreach⟩






theorem thinMapSideDarts_inter_offSeam_eventually_stage {d : ℕ × Bool}
    (hd : d ∈ thinMapSideDarts w hfin P B .left ∩ thinMapSideDarts w hfin P B .right)
    (hseam : d ∉ thinMapSeamDarts w P) :
    ∃ a ∈ thinMapSideSeeds w hfin P B .left,
      ∃ b ∈ thinMapSideSeeds w hfin P B .right,
        ∃ N, ∀ n ≥ N, ∃ ha : a.1 < (kmswStage w n).nextEdge,
          ∃ hb : b.1 < (kmswStage w n).nextEdge,
            ∃ hd : d.1 < (kmswStage w n).nextEdge,
              Relation.ReflTransGen (thinMapStageSideStep w hfin P B .left n)
                (⟨a.1, ha⟩, a.2) (⟨d.1, hd⟩, d.2) ∧
              Relation.ReflTransGen (thinMapStageSideStep w hfin P B .right n)
                (⟨b.1, hb⟩, b.2) (⟨d.1, hd⟩, d.2) := by
  have hleft : d ∈ thinMapSideClosure w hfin P B .left := hd.1.resolve_right hseam
  have hright : d ∈ thinMapSideClosure w hfin P B .right := hd.2.resolve_right hseam
  obtain ⟨a, ha, N, hN⟩ := thinMapSideClosure_eventually_stage w hfin P B .left hleft
  obtain ⟨b, hb, M, hM⟩ := thinMapSideClosure_eventually_stage w hfin P B .right hright
  refine ⟨a, ha, b, hb, max N M, fun n hn => ?_⟩
  obtain ⟨ha', hd', hchainLeft⟩ := hN n (le_trans (le_max_left _ _) hn)
  obtain ⟨hb', _, hchainRight⟩ := hM n (le_trans (le_max_right _ _) hn)
  exact ⟨ha', hb', hd', hchainLeft, hchainRight⟩

end DirectedDistances.PaperProofs.Section4
