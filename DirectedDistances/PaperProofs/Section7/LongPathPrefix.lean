module

public import DirectedDistances.KMSW.LeftmostGeodesicPlanar
public import DirectedDistances.KMSW.StageSubgraph






@[expose] public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW





theorem ldp_prefix_before_next_edge (w : ℕ → Fin 3) {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments) (T : ℕ) :
    IsLongest (P.initial T).2 ∧
      edgeWest w (P.edge T) = (P.initial T).1.id := by
  refine ⟨P.initial_isLongest w hP T, ?_⟩
  obtain ⟨_, hwest⟩ := P.edge_outgoing T
  have hend := pathEdgeList_endpoint (P.initial T).2
  rw [P.prefix_edges T] at hend
  exact hwest.trans hend

/-- Lift a limit arrow to the stage quiver when that edge is present there.
The edge ID and both endpoint IDs are retained. -/
private def stageArrowOfLimit {w : ℕ → Fin 3} (n : ℕ)
    {a b : PresentVertex w} (e : a ⟶ b)
    (he : e.val < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e.val = true) :
    (⟨a.id⟩ : StagePresentVertex w n) ⟶ ⟨b.id⟩ :=
  ⟨e.val, he.1, he.2,
    (edge_endpoints_eq w he.1).1.trans e.property.2.1,
    (edge_endpoints_eq w he.1).2.trans e.property.2.2⟩





theorem path_lifts_to_stage_of_edges_present
    (w : ℕ → Fin 3) (n : ℕ) {a b : PresentVertex w} (p : Path a b)
    (hp : ∀ e ∈ pathEdgeList p,
      e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true) :
    ∃ q : Path (⟨a.id⟩ : StagePresentVertex w n) ⟨b.id⟩,
      q.length = p.length := by
  revert hp
  induction p with
  | nil =>
      intro _
      exact ⟨Path.nil, rfl⟩
  | @cons y z p e ih =>
      intro hp
      have hpTail : ∀ f ∈ pathEdgeList p,
          f < (kmswStage w n).nextEdge ∧ (kmswStage w n).present f = true := by
        intro f hf
        apply hp f
        simp only [pathEdgeList, List.mem_append]
        exact Or.inl hf
      obtain ⟨q, hq⟩ := ih hpTail
      have he : e.val < (kmswStage w n).nextEdge ∧
          (kmswStage w n).present e.val = true :=
        hp e.val (by simp [pathEdgeList])
      refine ⟨q.cons (stageArrowOfLimit n e he), ?_⟩
      simp only [Path.length_cons, hq]






theorem stage_ldp_ge_prefix_length (w : ℕ → Fin 3) {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments)
    (T n : ℕ)
    (hp : ∀ e ∈ pathEdgeList (P.initial T).2,
      e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true) :
    ((P.initial T).2.length : WithBot ℕ) ≤
      ldpSup (⟨v⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩ := by
  let p := (P.initial T).2
  have hlong : IsLongest p := ldp_prefix_before_next_edge w P hP T |>.1
  obtain ⟨q, hq⟩ := path_lifts_to_stage_of_edges_present w n p hp
  have hpathBound {r : Path (⟨v⟩ : StagePresentVertex w n)
      ⟨(P.initial T).1.id⟩} : r.length ≤ p.length := by
    have hr := hlong ((stageToLimit w n).mapPath r)
    calc
      r.length = ((stageToLimit w n).mapPath r).length :=
        (stageToLimit_length w n r).symm
      _ ≤ p.length := hr
  have hbound : BddAbove
      (pathLengths (⟨v⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩) := by
    refine ⟨p.length, ?_⟩
    rintro m ⟨r, rfl⟩
    exact hpathBound
  have himage : BddAbove
      ((fun m : ℕ => (m : WithBot ℕ)) ''
        pathLengths (⟨v⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩) := by
    refine ⟨(p.length : WithBot ℕ), ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    rcases hm with ⟨r, rfl⟩
    exact WithBot.coe_le_coe.mpr hpathBound
  change (p.length : WithBot ℕ) ≤
    sSup ((fun m : ℕ => (m : WithBot ℕ)) ''
      pathLengths (⟨v⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩)
  apply le_csSup himage
  exact ⟨p.length, ⟨q, hq⟩, rfl⟩

end DirectedDistances.PaperProofs.Section7
