module

public import DirectedDistances.KMSW.StageTriangleCapSide
public import DirectedDistances.KMSW.MonotoneStepInvLEX

import all DirectedDistances.KMSW.MonotoneStepInvUP
import all DirectedDistances.KMSW.MonotoneStepInvLFR
import all DirectedDistances.KMSW.MonotoneStepInvLEX
import all DirectedDistances.KMSW.MonotoneStepAll
import all DirectedDistances.KMSW.MonotoneFamilyFaceData

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result. -/
theorem invariant_succ_lex_new_cap_dart_sides (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (hc : w j.val = 0) (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage w j.val).UL.dropLast.reverse = e :: es)
    {P : StageDrawing w j.val} (G : MonotoneStageInvariant w j.val P)
    (h : LayoutGood w (j.val + 1))
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : ¬ i.val < (kmswStage w j.val).triangles.length) :
    ∀ d ∈ stageTriangleDartList w j,
      (if d.2 then
        d.1 ∈ (invariant_succ_lex w j.val hc e es hUL G h).capUpper i
      else d.1 ∈ (invariant_succ_lex w j.val hc e es hUL G h).capLower i) := by
  have hcap :
      (invariant_succ_lex w j.val hc e es hUL G h).capLower i =
          [e, (kmswStage w j.val).active] ∧
        (invariant_succ_lex w j.val hc e es hUL G h).capUpper i =
          [(kmswStage w j.val).nextEdge] := by
    simp [invariant_succ_lex, hi]
  rw [stageTriangleDartList_left_existing_sides w j hc e es hUL]
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with hd | hd | hd
  · subst d
    simp [hcap.1]
  · subst d
    simp [hcap.1]
  · subst d
    simp [hcap.2]

end DirectedDistances.KMSW
