module

public import DirectedDistances.KMSW.MonotoneLimitDrawing
public import DirectedDistances.KMSW.KMSWConstructedRealization
public import DirectedDistances.KMSW.MonotoneLayoutDrawing

/-! # Monotone stage families

Helper toward the plane-realization obligation of adjudication n308; not a paper result.
Source conventions: `def-kmsw`, `remark-kmsw-infinite`, -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap DirectedDistances.RandomWalk Filter

noncomputable section

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] def MonotoneStepFrom (w : ℕ → Fin 3) (n : ℕ) : Prop :=
  ∀ {P : StageDrawing w n}, MonotoneStageInvariant w n P →
    ∃ h : LayoutGood w (n + 1),
      Nonempty (MonotoneStageInvariant w (n + 1) (monotoneLayoutDrawing w (n + 1) h))

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneStepFrom_of_cases (w : ℕ → Fin 3) (n : ℕ)
    (hACT : ∀ (_hc : w n = 2) (e : ℕ) (es : List ℕ),
      (kmswStage w n).UR = e :: es → MonotoneStepFrom w n)
    (hPEN : ∀ (_hc : w n = 2), (kmswStage w n).UR = [] → MonotoneStepFrom w n)
    (hUP : ∀ (_hc : w n = 1), MonotoneStepFrom w n)
    (hLEX : ∀ (_hc : w n = 0) (e : ℕ) (es : List ℕ),
      (kmswStage w n).UL.dropLast.reverse = e :: es → MonotoneStepFrom w n)
    (hLFR : ∀ (_hc : w n = 0),
      (kmswStage w n).UL.dropLast.reverse = [] → MonotoneStepFrom w n) :
    MonotoneStepFrom w n := by
  rcases (show w n = 0 ∨ w n = 1 ∨ w n = 2 from by omega) with hc | hc | hc
  · cases hs : (kmswStage w n).UL.dropLast.reverse with
    | nil => exact hLFR hc hs
    | cons e es => exact hLEX hc e es hs
  · exact hUP hc
  · cases hs : (kmswStage w n).UR with
    | nil => exact hPEN hc hs
    | cons e es => exact hACT hc e es hs

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotone_family (w : ℕ → Fin 3) (hstep : ∀ n, MonotoneStepFrom w n) :
    ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)) := by
  intro n
  induction n with
  | zero =>
    exact ⟨layoutGood_of_invariant (kmswStage0MonotoneInvariant w),
      ⟨invariant_layoutDrawing (kmswStage0MonotoneInvariant w)⟩⟩
  | succ n ih =>
    obtain ⟨h, ⟨G⟩⟩ := ih
    exact hstep n G

private theorem layoutPos_succ_old_vertex (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    layoutPos w (n + 1) v = layoutPos w n v := by
  have hne : v ≠ (kmswStage w n).nextVertex := by omega
  simp [layoutPos, kmswStageRank, layoutHeight, hne]

private theorem layoutArc_succ_old_edge (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    layoutArc w (n + 1) e = layoutArc w n e := by
  simp only [layoutArc, ite_eq_left he]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem stageExtends_monotoneLayout (w : ℕ → Fin 3) (n : ℕ)
    (h : LayoutGood w n) (h' : LayoutGood w (n + 1)) :
    StageExtends w n (monotoneLayoutDrawing w n h)
      (monotoneLayoutDrawing w (n + 1) h') := by
  constructor
  · intro v
    exact (layoutPos_succ_old_vertex w n v.val v.isLt).symm
  · rintro ⟨e, b⟩
    change (if b then (layoutArc w n e.val).reverse else layoutArc w n e.val) =
      (if b then (layoutArc w (n + 1) e.val).reverse else layoutArc w (n + 1) e.val)
    rw [layoutArc_succ_old_edge w n e.val e.isLt]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] noncomputable def monotoneFamilyDrawing (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h))) :
    PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w) :=
  monotoneLimitDrawing w hfin (fun n =>
    ⟨monotoneLayoutDrawing w n (hfam n).choose, (hfam n).choose_spec⟩)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem kmswConstructedPlaneRealization_of_family (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)))
    (hface : let P := monotoneFamilyDrawing w hfin hfam
      ∃ U : P.Face, P.IsUnbounded U ∧
        (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
        ∀ d, P.dartBorders d U ↔ limitExternalDart w d) :
    KMSWConstructedPlaneRealizationStatement w hfin htrans hR hL0 := by
  let Q : ∀ n, StageDrawing w n := fun n => monotoneLayoutDrawing w n (hfam n).choose
  let family : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P) :=
    fun n => ⟨Q n, (hfam n).choose_spec⟩
  have hagree := monotoneLimitDrawing_agrees w hfin family Q
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨Q, (fun n => stageExtends_monotoneLayout w n (hfam n).choose
    (hfam (n + 1)).choose), monotoneFamilyDrawing w hfin hfam,
    hagree.1, hagree.2, hface⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem kmswConstructedPlaneRealization_of_steps (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (hstep : ∀ n, MonotoneStepFrom w n)
    (hface : let P := monotoneFamilyDrawing w hfin (monotone_family w hstep)
      ∃ U : P.Face, P.IsUnbounded U ∧
        (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
        ∀ d, P.dartBorders d U ↔ limitExternalDart w d) :
    KMSWConstructedPlaneRealizationStatement w hfin htrans hR hL0 :=
  kmswConstructedPlaneRealization_of_family w hfin htrans hR hL0
    (monotone_family w hstep) hface

end
end DirectedDistances.KMSW
