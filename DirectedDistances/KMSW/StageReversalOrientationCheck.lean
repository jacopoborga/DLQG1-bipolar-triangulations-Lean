module

public import DirectedDistances.KMSW.StageRotation

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalCodeOne : ℕ → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | _ => 0

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalCodeOneReverse : ℕ → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | _ => 0

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalCodeTwo : ℕ → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 1
  | _ => 0

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalCodeTwoReverse : ℕ → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 1
  | _ => 0

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeOneData :
    (List.ofFn fun i : Fin 5 => reversalCodeOne i.val) = [1, 2, 0, 1, 2] ∧
    (List.ofFn fun i : Fin 5 => reversalCodeOneReverse i.val) = [2, 0, 1, 2, 0] := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeTwoData :
    (List.ofFn fun i : Fin 5 => reversalCodeTwo i.val) = [0, 1, 2, 0, 1] ∧
    (List.ofFn fun i : Fin 5 => reversalCodeTwoReverse i.val) = [0, 1, 2, 0, 1] := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeDefaults :
    reversalCodeOne 5 = 0 ∧ reversalCodeOneReverse 5 = 0 ∧
    reversalCodeTwo 5 = 0 ∧ reversalCodeTwoReverse 5 = 0 := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeOneStageSize :
    (kmswStage reversalCodeOne 5).nextEdge = 6 ∧
    (kmswStage reversalCodeOneReverse 5).nextEdge = 6 := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeOneStageData :
    (List.ofFn fun e : Fin 6 => (kmswStage reversalCodeOne 5).present e.val) =
      [true, true, true, true, true, true] ∧
    (List.ofFn fun e : Fin 6 =>
      ((kmswStage reversalCodeOne 5).west e.val,
        (kmswStage reversalCodeOne 5).east e.val)) =
      [(0, 1), (0, 2), (2, 1), (0, 1), (0, 3), (3, 1)] ∧
    (List.ofFn fun e : Fin 6 =>
      ((kmswStage reversalCodeOneReverse 5).west e.val,
        (kmswStage reversalCodeOneReverse 5).east e.val)) =
      [(0, 1), (1, 2), (0, 2), (0, 3), (3, 2), (0, 2)] ∧
    (kmswStage reversalCodeOne 5).UL = [4, 5] ∧
    (kmswStage reversalCodeOne 5).UR = [] ∧
    (kmswStage reversalCodeOne 5).LL = [] ∧
    (kmswStage reversalCodeOne 5).LR = [0] ∧
    (kmswStage reversalCodeOneReverse 5).UL = [5] ∧
    (kmswStage reversalCodeOneReverse 5).UR = [] ∧
    (kmswStage reversalCodeOneReverse 5).LL = [] ∧
    (kmswStage reversalCodeOneReverse 5).LR = [0, 1] := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeTwoStageSize :
    (kmswStage reversalCodeTwo 5).nextEdge = 8 ∧
    (kmswStage reversalCodeTwoReverse 5).nextEdge = 8 := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeTwoStageData :
    (List.ofFn fun e : Fin 8 => (kmswStage reversalCodeTwo 5).present e.val) =
      [true, true, false, true, true, true, true, false] ∧
    (List.ofFn fun e : Fin 8 =>
      ((kmswStage reversalCodeTwo 5).west e.val,
        (kmswStage reversalCodeTwo 5).east e.val)) =
      [(0, 1), (2, 1), (2, 0), (2, 3), (3, 1), (2, 1), (2, 4), (4, 1)] ∧
    (kmswStage reversalCodeTwo 5).UL = [6] ∧
    (kmswStage reversalCodeTwo 5).UR = [7] ∧
    (kmswStage reversalCodeTwo 5).LL = [2] ∧
    (kmswStage reversalCodeTwo 5).LR = [0] := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalEpsilonOne (e : Fin 6) : Fin 6 := ⟨5 - e.val, by omega⟩

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalEpsilonOneTable :
    List.ofFn reversalEpsilonOne = [5, 4, 3, 2, 1, 0] := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalEpsilonTwo (e : Fin 8) : Fin 8 :=
  if e.val = 0 then 6 else if e.val = 1 then 5 else if e.val = 2 then 7 else
  if e.val = 3 then 4 else if e.val = 4 then 3 else if e.val = 5 then 1 else
  if e.val = 6 then 0 else 2

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalEpsilonTwoTable :
    List.ofFn reversalEpsilonTwo = [6, 5, 7, 4, 3, 1, 0, 2] := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalPsiOne (d : StageDart 6) : StageDart 6 :=
  (reversalEpsilonOne d.1, !d.2)

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalPsiOneNoFlip (d : StageDart 6) : StageDart 6 :=
  (reversalEpsilonOne d.1, d.2)

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalPsiTwo (d : StageDart 8) : StageDart 8 :=
  (reversalEpsilonTwo d.1, !d.2)

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalPsiTwoNoFlip (d : StageDart 8) : StageDart 8 :=
  (reversalEpsilonTwo d.1, d.2)

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalEpsilonOneStage
    (e : Fin (kmswStage reversalCodeOneReverse 5).nextEdge) :
    Fin (kmswStage reversalCodeOne 5).nextEdge :=
  if e.val = 0 then ⟨5, by have h := reversalCodeOneStageSize.1; omega⟩ else
  if e.val = 1 then ⟨4, by have h := reversalCodeOneStageSize.1; omega⟩ else
  if e.val = 2 then ⟨3, by have h := reversalCodeOneStageSize.1; omega⟩ else
  if e.val = 3 then ⟨2, by have h := reversalCodeOneStageSize.1; omega⟩ else
  if e.val = 4 then ⟨1, by have h := reversalCodeOneStageSize.1; omega⟩ else
  ⟨0, by have h := reversalCodeOneStageSize.1; omega⟩

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalEpsilonTwoStage
    (e : Fin (kmswStage reversalCodeTwoReverse 5).nextEdge) :
    Fin (kmswStage reversalCodeTwo 5).nextEdge :=
  if e.val = 0 then ⟨6, by have h := reversalCodeTwoStageSize.1; omega⟩ else
  if e.val = 1 then ⟨5, by have h := reversalCodeTwoStageSize.1; omega⟩ else
  if e.val = 2 then ⟨7, by have h := reversalCodeTwoStageSize.1; omega⟩ else
  if e.val = 3 then ⟨4, by have h := reversalCodeTwoStageSize.1; omega⟩ else
  if e.val = 4 then ⟨3, by have h := reversalCodeTwoStageSize.1; omega⟩ else
  if e.val = 5 then ⟨1, by have h := reversalCodeTwoStageSize.1; omega⟩ else
  if e.val = 6 then ⟨0, by have h := reversalCodeTwoStageSize.1; omega⟩ else
  ⟨2, by have h := reversalCodeTwoStageSize.1; omega⟩

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞}
plane realization); not a paper result. -/
theorem reversalEpsilonStageTables :
    List.ofFn (fun e : Fin (kmswStage reversalCodeOneReverse 5).nextEdge =>
      (reversalEpsilonOneStage e).val) =
        [5, 4, 3, 2, 1, 0] ∧
    List.ofFn (fun e : Fin (kmswStage reversalCodeTwoReverse 5).nextEdge =>
      (reversalEpsilonTwoStage e).val) =
        [6, 5, 7, 4, 3, 1, 0, 2] := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞}
plane realization); not a paper result. -/
theorem reversalEpsilonStageActive :
    ∀ s : Fin 6,
      reversalEpsilonOneStage
        ⟨(kmswStage reversalCodeOneReverse s.val).active,
          act_lt_nextEdge reversalCodeOneReverse (by omega)⟩ =
        ⟨(kmswStage reversalCodeOne (5 - s.val)).active,
          act_lt_nextEdge reversalCodeOne (by omega)⟩ ∧
      reversalEpsilonTwoStage
        ⟨(kmswStage reversalCodeTwoReverse s.val).active,
          act_lt_nextEdge reversalCodeTwoReverse (by omega)⟩ =
        ⟨(kmswStage reversalCodeTwo (5 - s.val)).active,
          act_lt_nextEdge reversalCodeTwo (by omega)⟩ := by
  decide +revert

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞}
plane realization); not a paper result. -/
theorem reversalEpsilonTwoMissingStackPositions :
    reversalEpsilonTwoStage
        ⟨2, by have h := reversalCodeTwoStageSize.2; omega⟩ =
      ⟨7, by have h := reversalCodeTwoStageSize.1; omega⟩ ∧
    reversalEpsilonTwoStage
        ⟨7, by have h := reversalCodeTwoStageSize.2; omega⟩ =
      ⟨2, by have h := reversalCodeTwoStageSize.1; omega⟩ := by
  decide

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalPsiOneStage
    (d : StageDart (kmswStage reversalCodeOneReverse 5).nextEdge) :
    StageDart (kmswStage reversalCodeOne 5).nextEdge :=
  (reversalEpsilonOneStage d.1, !d.2)

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalPsiOneStageNoFlip
    (d : StageDart (kmswStage reversalCodeOneReverse 5).nextEdge) :
    StageDart (kmswStage reversalCodeOne 5).nextEdge :=
  (reversalEpsilonOneStage d.1, d.2)

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalPsiTwoStage
    (d : StageDart (kmswStage reversalCodeTwoReverse 5).nextEdge) :
    StageDart (kmswStage reversalCodeTwo 5).nextEdge :=
  (reversalEpsilonTwoStage d.1, !d.2)

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
def reversalPsiTwoStageNoFlip
    (d : StageDart (kmswStage reversalCodeTwoReverse 5).nextEdge) :
    StageDart (kmswStage reversalCodeTwo 5).nextEdge :=
  (reversalEpsilonTwoStage d.1, d.2)

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeOnePsiCommutes :
    ∀ d : StageDart (kmswStage reversalCodeOneReverse 5).nextEdge,
      reversalPsiOneStage (stageRot reversalCodeOneReverse 5 d) =
        stageRot reversalCodeOne 5 (reversalPsiOneStage d) := by
  decide +revert

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeOnePsiMirror_fails :
    ∃ d : StageDart (kmswStage reversalCodeOneReverse 5).nextEdge,
      reversalPsiOneStage (stageRot reversalCodeOneReverse 5 d) ≠
        (stageRot reversalCodeOne 5).symm (reversalPsiOneStage d) := by
  refine ⟨(⟨0, by have h := reversalCodeOneStageSize.2; omega⟩, false), by decide⟩

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeOnePsiNoFlipCommutes_fails :
    ∃ d : StageDart (kmswStage reversalCodeOneReverse 5).nextEdge,
      reversalPsiOneStageNoFlip (stageRot reversalCodeOneReverse 5 d) ≠
        stageRot reversalCodeOne 5 (reversalPsiOneStageNoFlip d) := by
  refine ⟨(⟨0, by have h := reversalCodeOneStageSize.2; omega⟩, false), by decide⟩

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeOnePsiNoFlipMirror_fails :
    ∃ d : StageDart (kmswStage reversalCodeOneReverse 5).nextEdge,
      reversalPsiOneStageNoFlip (stageRot reversalCodeOneReverse 5 d) ≠
        (stageRot reversalCodeOne 5).symm (reversalPsiOneStageNoFlip d) := by
  refine ⟨(⟨0, by have h := reversalCodeOneStageSize.2; omega⟩, false), by decide⟩

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeTwoPsiCommutes :
    ∀ d : StageDart (kmswStage reversalCodeTwoReverse 5).nextEdge,
      reversalPsiTwoStage (stageRot reversalCodeTwoReverse 5 d) =
        stageRot reversalCodeTwo 5 (reversalPsiTwoStage d) := by
  decide +revert

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeTwoPsiMirror_fails :
    ∃ d : StageDart (kmswStage reversalCodeTwoReverse 5).nextEdge,
      reversalPsiTwoStage (stageRot reversalCodeTwoReverse 5 d) ≠
        (stageRot reversalCodeTwo 5).symm (reversalPsiTwoStage d) := by
  refine ⟨(⟨0, by have h := reversalCodeTwoStageSize.2; omega⟩, true), by decide⟩

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeTwoPsiNoFlipCommutes_fails :
    ∃ d : StageDart (kmswStage reversalCodeTwoReverse 5).nextEdge,
      reversalPsiTwoStageNoFlip (stageRot reversalCodeTwoReverse 5 d) ≠
        stageRot reversalCodeTwo 5 (reversalPsiTwoStageNoFlip d) := by
  refine ⟨(⟨0, by have h := reversalCodeTwoStageSize.2; omega⟩, false), by decide⟩

/-- Helper toward Theorem 1.4 (KMSW reversal orientation check for the M_{0,∞} -/
theorem reversalCodeTwoPsiNoFlipMirror_fails :
    ∃ d : StageDart (kmswStage reversalCodeTwoReverse 5).nextEdge,
      reversalPsiTwoStageNoFlip (stageRot reversalCodeTwoReverse 5 d) ≠
        (stageRot reversalCodeTwo 5).symm (reversalPsiTwoStageNoFlip d) := by
  refine ⟨(⟨0, by have h := reversalCodeTwoStageSize.2; omega⟩, false), by decide⟩

/-! Summary: For each code, the edge-flipping map `Psi` commutes with stage
rotation. The no-flip map `Psi'` satisfies neither commutation nor conjugation
to the inverse. These finite checks are helpers, not paper results. -/

end DirectedDistances.KMSW
