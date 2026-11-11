module

public import DirectedDistances.KMSW.StageFrontier

/-! # Tails of active edges on old upper boundaries

Helpers toward Lemma 7.13 of `finite.tex`. -/

public section
namespace DirectedDistances.KMSW





theorem kmswStage_tail_mem_up (w : ℕ → Fin 3) {N m : ℕ} (hNm : N ≤ m)
    (hOld : (kmswStage w m).west (kmswStage w m).active <
      (kmswStage w N).nextVertex) :
    ∃ e ∈ (kmswStage w N).UL ++ (kmswStage w N).UR,
      (kmswStage w N).west e = (kmswStage w m).west (kmswStage w m).active ∨
        (kmswStage w N).east e = (kmswStage w m).west (kmswStage w m).active := by
  have hactiveUL : (kmswStage w m).active ∈ (kmswStage w m).UL := by
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last w m
    rw [hUL]
    simp
  have hupper : (kmswStage w m).active ∈
      (kmswStage w m).UL ++ (kmswStage w m).UR :=
    List.mem_append_left _ hactiveUL
  have hendpoints :=
    kmswStage_upperFrontier_endpoints w N m hNm
      (kmswStage w m).active hupper
  have hfrontier :
      (∃ e, e ∈ (kmswStage w N).UL ++ (kmswStage w N).UR ∧
        ((kmswStage w N).west e =
            (kmswStage w m).west (kmswStage w m).active ∨
          (kmswStage w N).east e =
            (kmswStage w m).west (kmswStage w m).active)) ∨
        (kmswStage w N).nextVertex ≤
          (kmswStage w m).west (kmswStage w m).active := by
    simpa only [UpperFrontierEndpoint] using hendpoints.1
  rcases hfrontier with ⟨e, he, htail⟩ | hfresh
  · exact ⟨e, he, htail⟩
  · omega

end DirectedDistances.KMSW
