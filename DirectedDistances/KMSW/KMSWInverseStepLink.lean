module

public import DirectedDistances.KMSW.KMSWInverseCode
public import DirectedDistances.PlanarMap.BipolarPeanoConfiguration
public import DirectedDistances.KMSW.StageRotation

/-! # Inverse codes and local Peano steps

Helper toward thm-kmsw surjectivity
order. The λ-order via `peanoEdge` is identified with the manuscript's
first-visit order by `DirectedDistances.PlanarMap.peanoEdge_increasing_firstVisit`
(`BipolarPeanoFirstVisit.lean`). -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable {ℓ r n : ℕ}

/-- Helper toward thm-kmsw surjectivity
identifies the inverse code with the local Peano height increment. -/
theorem kmswRepInverseCode_eq_stepCode_peanoStepHeightDifference
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    kmswRepInverseCode R ⟨j, by omega⟩ =
      stepCode (peanoStepHeightDifference R.B j
        (by simpa only [R.edges] using hj)) := by
  unfold kmswRepInverseCode codesOfWalk kmswRepInverseWalk
  congr 1
  apply Prod.ext <;>
    simp [bipolarInverseWalk, peanoStepHeightDifference]

private theorem stepCode_peanoStepHeightDifference_eq_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) (k : PeanoStepKind) :
    stepCode (peanoStepHeightDifference B j hj) = stepCode k.increment ↔
      peanoStepKind B j hj = k := by
  rw [peanoStepConfig_height_increment B j hj _ (peanoStepKind_config B j hj)]
  cases peanoStepKind B j hj <;> cases k <;>
    simp [PeanoStepKind.increment, stepCode]

/-- Helper toward thm-kmsw surjectivity -/
theorem kmswRepInverseCode_eq_two_iff_peanoStepKind_descend
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    kmswRepInverseCode R ⟨j, by omega⟩ = 2 ↔
      peanoStepKind R.B j (by simpa only [R.edges] using hj) = .descend := by
  rw [kmswRepInverseCode_eq_stepCode_peanoStepHeightDifference R j hj]
  exact stepCode_peanoStepHeightDifference_eq_iff R.B j _ .descend

/-- Helper toward thm-kmsw surjectivity -/
theorem kmswRepInverseCode_eq_zero_iff_peanoStepKind_climb
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    kmswRepInverseCode R ⟨j, by omega⟩ = 0 ↔
      peanoStepKind R.B j (by simpa only [R.edges] using hj) = .climb := by
  rw [kmswRepInverseCode_eq_stepCode_peanoStepHeightDifference R j hj]
  exact stepCode_peanoStepHeightDifference_eq_iff R.B j _ .climb

/-- Helper toward thm-kmsw surjectivity -/
theorem kmswRepInverseCode_eq_one_iff_peanoStepKind_rotate
    (R : KMSWMapRep ℓ r n) (j : ℕ) (hj : j + 1 < n) :
    kmswRepInverseCode R ⟨j, by omega⟩ = 1 ↔
      peanoStepKind R.B j (by simpa only [R.edges] using hj) = .rotate := by
  rw [kmswRepInverseCode_eq_stepCode_peanoStepHeightDifference R j hj]
  exact stepCode_peanoStepHeightDifference_eq_iff R.B j _ .rotate

/-- Helper toward thm-kmsw surjectivity
these are projections of the existing `kmswStepOfStep` update. -/
theorem kmswStage_step_leftExisting_facts
    (u : ℕ → Fin 3) (m e : ℕ) (es : List ℕ)
    (hc : u m = 0) (hUL : (kmswStage u m).UL.dropLast.reverse = e :: es) :
    let s := kmswStage u m
    let t := kmswStage u (m + 1)
    t.nextEdge = s.nextEdge + 1 ∧ t.nextVertex = s.nextVertex ∧
      t.west s.nextEdge = s.west e ∧ t.east s.nextEdge = s.east s.active ∧
      t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
      t.UL = es.reverse ++ [s.nextEdge] ∧ t.LR = s.LR ∧
      t.UR = s.UR ∧ t.LL = s.LL := by
  have hcode : kmswCodeStep (u m) = .left := by rw [hc]; rfl
  dsimp only
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hUL, State.addEdge]

/-- Helper toward thm-kmsw surjectivity
and a geometric missing LL edge. -/
theorem kmswStage_step_leftFresh_facts
    (u : ℕ → Fin 3) (m : ℕ) (hc : u m = 0)
    (hUL : (kmswStage u m).UL.dropLast.reverse = []) :
    let s := kmswStage u m
    let t := kmswStage u (m + 1)
    t.nextEdge = s.nextEdge + 2 ∧ t.nextVertex = s.nextVertex + 1 ∧
      t.west s.nextEdge = s.nextVertex ∧ t.east s.nextEdge = s.east s.active ∧
      t.west (s.nextEdge + 1) = s.nextVertex ∧
      t.east (s.nextEdge + 1) = s.west s.active ∧
      t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
      t.present (s.nextEdge + 1) = false ∧
      t.UL = [s.nextEdge] ∧ t.LR = s.LR ∧ t.UR = s.UR ∧
      t.LL = (s.nextEdge + 1) :: s.LL := by
  have hcode : kmswCodeStep (u m) = .left := by rw [hc]; rfl
  dsimp only
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hUL, State.addEdge]

/-- Helper toward thm-kmsw surjectivity
and a geometric missing UR edge. -/
theorem kmswStage_step_up_facts
    (u : ℕ → Fin 3) (m : ℕ) (hc : u m = 1) :
    let s := kmswStage u m
    let t := kmswStage u (m + 1)
    t.nextEdge = s.nextEdge + 2 ∧ t.nextVertex = s.nextVertex + 1 ∧
      t.west s.nextEdge = s.west s.active ∧ t.east s.nextEdge = s.nextVertex ∧
      t.west (s.nextEdge + 1) = s.nextVertex ∧
      t.east (s.nextEdge + 1) = s.east s.active ∧
      t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
      t.present (s.nextEdge + 1) = false ∧
      t.UL = s.UL.dropLast ++ [s.nextEdge] ∧ t.LR = s.LR ∧
      t.UR = (s.nextEdge + 1) :: s.UR ∧ t.LL = s.LL := by
  have hcode : kmswCodeStep (u m) = .up := by rw [hc]; rfl
  dsimp only
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, State.addEdge]

/-- Helper toward thm-kmsw surjectivity
edge; no geometric edge, vertex, or endpoint is changed. -/
theorem kmswStage_step_activation_facts
    (u : ℕ → Fin 3) (m e : ℕ) (es : List ℕ)
    (hc : u m = 2) (hUR : (kmswStage u m).UR = e :: es) :
    let s := kmswStage u m
    let t := kmswStage u (m + 1)
    t.nextEdge = s.nextEdge ∧ t.nextVertex = s.nextVertex ∧
      t.west = s.west ∧ t.east = s.east ∧
      t.active = e ∧ t.present e = true ∧
      (∀ f, t.present f = if f = e then true else s.present f) ∧
      t.UL = s.UL ++ [e] ∧ t.LR = s.LR ∧ t.UR = es ∧ t.LL = s.LL := by
  have hcode : kmswCodeStep (u m) = .down := by rw [hc]; rfl
  dsimp only
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hUR]

/-- Helper toward thm-kmsw surjectivity
pendant edge when the UR boundary is empty. -/
theorem kmswStage_step_pendant_facts
    (u : ℕ → Fin 3) (m : ℕ) (hc : u m = 2)
    (hUR : (kmswStage u m).UR = []) :
    let s := kmswStage u m
    let t := kmswStage u (m + 1)
    t.nextEdge = s.nextEdge + 1 ∧ t.nextVertex = s.nextVertex + 1 ∧
      t.west s.nextEdge = s.east s.active ∧ t.east s.nextEdge = s.nextVertex ∧
      t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
      t.UL = s.UL ++ [s.nextEdge] ∧ t.LR = s.LR ++ [s.nextEdge] ∧
      t.UR = [] ∧ t.LL = s.LL := by
  have hcode : kmswCodeStep (u m) = .down := by rw [hc]; rfl
  dsimp only
  simp [kmswStage, kmswStep, hcode, kmswStepOfStep, hUR, State.addEdge]

end DirectedDistances.KMSW
