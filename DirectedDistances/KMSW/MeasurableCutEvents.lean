module

public import DirectedDistances.KMSW.CutEquivalence
public import DirectedDistances.RandomWalk.PitmanCodes
import Mathlib.Order.Interval.Finset.Basic

/-! # Measurability of the cut-vertex events on code space

Prop 4.3 / Lemma 4.8 commands: transferring an almost-sure statement from the coupled
realization to an arbitrary realization needs the events to be measurable. The events
only proves measurability on `ℕ → Fin 3` with the product σ-algebra. It is a helper, not a
paper result. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk

/-- Extension of a finite prefix by the constant code `0`. -/
private def extendPrefix (n : ℕ) (x : Fin n → Fin 3) : ℕ → Fin 3 :=
  fun i => if h : i < n then x ⟨i, h⟩ else 0

private theorem measurable_restrictPrefix (n : ℕ) :
    Measurable (fun (w : ℕ → Fin 3) (i : Fin n) => w i) := by
  fun_prop

/-- A function on code space that depends only on the first `n` codes is measurable
(helper for SA43). -/
theorem measurable_of_factors_prefix {β : Type*} [MeasurableSpace β] (n : ℕ)
    (f : (ℕ → Fin 3) → β)
    (h : ∀ w w' : ℕ → Fin 3, (∀ i < n, w i = w' i) → f w = f w') :
    Measurable f := by
  have hf : f = (fun x => f (extendPrefix n x)) ∘ (fun (w : ℕ → Fin 3) (i : Fin n) => w i) := by
    funext w
    apply h
    intro i hi
    simp [extendPrefix, hi]
  rw [hf]
  exact (measurable_of_finite _).comp (measurable_restrictPrefix n)

/-- A predicate on code space that factors through the restriction to `Fin n` defines a
measurable set (helper for SA43). -/
theorem measurableSet_of_factors_prefix (n : ℕ) (P : (ℕ → Fin 3) → Prop)
    (h : ∀ w w' : ℕ → Fin 3, (∀ i < n, w i = w' i) → (P w ↔ P w')) :
    MeasurableSet {w | P w} := by
  have hf : {w | P w} = (fun (w : ℕ → Fin 3) (i : Fin n) => w i) ⁻¹'
      {x | P (extendPrefix n x)} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    apply h
    intro i hi
    simp [extendPrefix, hi]
  rw [hf]
  exact (Set.toFinite _).measurableSet.preimage (measurable_restrictPrefix n)

/-- Stage `n` of `def-kmsw` depends only on the first `n` codes. -/
theorem kmswStage_congr {w w' : ℕ → Fin 3} {n : ℕ} (h : ∀ i < n, w i = w' i) :
    kmswStage w n = kmswStage w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change kmswStep (kmswStage w n) (w n) = kmswStep (kmswStage w' n) (w' n)
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- `L w n` depends only on the first `n` codes. -/
theorem L_congr {w w' : ℕ → Fin 3} {n : ℕ} (h : ∀ i < n, w i = w' i) : L w n = L w' n := by
  unfold L
  exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])

/-- `R w n` depends only on the first `n` codes. -/
theorem R_congr {w w' : ℕ → Fin 3} {n : ℕ} (h : ∀ i < n, w i = w' i) : R w n = R w' n := by
  unfold R
  exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])

/-- Any predicate of stage `n` is measurable in the code sequence (SA43 caveat). -/
theorem measurableSet_stage (n : ℕ) (Q : State → Prop) :
    MeasurableSet {w : ℕ → Fin 3 | Q (kmswStage w n)} :=
  measurableSet_of_factors_prefix n _ (fun _ _ h => by rw [kmswStage_congr h])

/-- Any predicate of `L w n` is measurable in the code sequence (SA43 caveat). -/
theorem measurableSet_L (n : ℕ) (Q : ℤ → Prop) :
    MeasurableSet {w : ℕ → Fin 3 | Q (L w n)} :=
  measurableSet_of_factors_prefix n _ (fun _ _ h => by rw [L_congr h])

/-- Any predicate of `R w n` is measurable in the code sequence (SA43 caveat). -/
theorem measurableSet_R (n : ℕ) (Q : ℤ → Prop) :
    MeasurableSet {w : ℕ → Fin 3 | Q (R w n)} :=
  measurableSet_of_factors_prefix n _ (fun _ _ h => by rw [R_congr h])

private theorem infinite_iff_forall_exists_ge (s : Set ℕ) :
    s.Infinite ↔ ∀ N, ∃ j, N ≤ j ∧ j ∈ s := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨b, hb, hlt⟩ := h N
    exact ⟨b, hlt.le, hb⟩
  · intro h N
    obtain ⟨b, hb, hbs⟩ := h (N + 1)
    exact ⟨b, hbs, by omega⟩

private theorem finite_iff_bound (s : Set ℕ) : s.Finite ↔ ∃ B, ∀ e ∈ s, e < B := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := h.bddAbove
    exact ⟨B + 1, fun e he => Nat.lt_succ_of_le (hB he)⟩
  · rintro ⟨B, hB⟩
    exact (Set.finite_Iio B).subset (fun e he => hB e he)

/-- Measurability of the finite-incidence event of SA43: every vertex meets finitely many -/
theorem measurableSet_finiteIncidence :
    MeasurableSet {w : ℕ → Fin 3 | ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite} := by
  have : {w : ℕ → Fin 3 | ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite} =
      ⋂ v : ℕ, ⋃ B : ℕ, ⋂ e : ℕ, ⋂ (_ : B ≤ e), ⋂ n : ℕ,
        {w : ℕ → Fin 3 | ¬ (e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v))} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    refine forall_congr' (fun v => ?_)
    rw [finite_iff_bound]
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨B, fun e heB n hn => ?_⟩
      exact absurd (hB e ⟨n, hn⟩) (by omega)
    · rintro ⟨B, hB⟩
      refine ⟨B, fun e ⟨n, hn⟩ => ?_⟩
      by_contra hlt
      exact hB e (by omega) n hn
  rw [this]
  refine MeasurableSet.iInter (fun v => MeasurableSet.iUnion (fun B => ?_))
  refine MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun _ => MeasurableSet.iInter
    (fun n => ?_)))
  exact measurableSet_stage n (fun s => ¬ (e < s.nextEdge ∧ (s.west e = v ∨ s.east e = v)))

/-- Measurability of the transience event `L w → ∞` (SA43 caveat; `def-uiqbot`). -/
theorem measurableSet_tendsto_L :
    MeasurableSet {w : ℕ → Fin 3 | Tendsto (L w) atTop atTop} := by
  have : {w : ℕ → Fin 3 | Tendsto (L w) atTop atTop} =
      ⋂ b : ℤ, ⋃ i : ℕ, ⋂ a : ℕ, ⋂ (_ : i ≤ a), {w : ℕ → Fin 3 | b ≤ L w a} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, tendsto_atTop_atTop]
  rw [this]
  exact MeasurableSet.iInter (fun b => MeasurableSet.iUnion (fun i =>
    MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun _ => measurableSet_L a _))))

/-- Measurability of `∀ a, ∃ n, R w n ≤ a` (SA43 caveat; `def-uiqbot`). -/
theorem measurableSet_R_unbounded_below :
    MeasurableSet {w : ℕ → Fin 3 | ∀ a : ℤ, ∃ n, R w n ≤ a} := by
  have : {w : ℕ → Fin 3 | ∀ a : ℤ, ∃ n, R w n ≤ a} =
      ⋂ a : ℤ, ⋃ n : ℕ, {w : ℕ → Fin 3 | R w n ≤ a} := by
    ext w
    simp
  rw [this]
  exact MeasurableSet.iInter (fun a => MeasurableSet.iUnion (fun n => measurableSet_R n (fun x => x ≤ a)))

/-- Measurability of `∀ j, 0 ≤ L w j` (SA43 caveat; `def-uiqbot`). -/
theorem measurableSet_L_nonneg :
    MeasurableSet {w : ℕ → Fin 3 | ∀ j, 0 ≤ L w j} := by
  have : {w : ℕ → Fin 3 | ∀ j, 0 ≤ L w j} = ⋂ j : ℕ, {w : ℕ → Fin 3 | 0 ≤ L w j} := by
    ext w
    simp
  rw [this]
  exact MeasurableSet.iInter (fun j => measurableSet_L j _)

private theorem measurableSet_leftBoundaryEdge (e : ℕ) :
    MeasurableSet {w : ℕ → Fin 3 | IsLeftBoundaryEdge w e} := by
  have : {w : ℕ → Fin 3 | IsLeftBoundaryEdge w e} =
      ⋂ N : ℕ, ⋃ j : ℕ, ⋃ (_ : N ≤ j), {w : ℕ → Fin 3 | e ∈ (kmswStage w j).UL} := by
    ext w
    simp only [IsLeftBoundaryEdge, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
    exact infinite_iff_forall_exists_ge _
  rw [this]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun j => MeasurableSet.iUnion
    (fun _ => measurableSet_stage j (fun s => e ∈ s.UL))))

private theorem measurableSet_rightBoundaryEdge (e : ℕ) :
    MeasurableSet {w : ℕ → Fin 3 | IsRightBoundaryEdge w e} := by
  have : {w : ℕ → Fin 3 | IsRightBoundaryEdge w e} =
      ⋂ N : ℕ, ⋃ j : ℕ, ⋃ (_ : N ≤ j), {w : ℕ → Fin 3 | e ∈ (kmswStage w j).LR} := by
    ext w
    simp only [IsRightBoundaryEdge, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
    exact infinite_iff_forall_exists_ge _
  rw [this]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun j => MeasurableSet.iUnion
    (fun _ => measurableSet_stage j (fun s => e ∈ s.LR))))

private theorem measurableSet_endpoint (e v : ℕ) :
    MeasurableSet {w : ℕ → Fin 3 | edgeWest w e = v ∨ edgeEast w e = v} :=
  measurableSet_stage e (fun s => s.west e = v ∨ s.east e = v)

/-- Measurability of `{w | IsCutVertex w v}` for each `v` (`prop-cut-vertex`, -/
theorem measurableSet_isCutVertex (v : ℕ) :
    MeasurableSet {w : ℕ → Fin 3 | IsCutVertex w v} := by
  have : {w : ℕ → Fin 3 | IsCutVertex w v} =
      (⋃ e : ℕ, {w : ℕ → Fin 3 | IsLeftBoundaryEdge w e} ∩
        {w | edgeWest w e = v ∨ edgeEast w e = v}) ∩
      (⋃ e : ℕ, {w : ℕ → Fin 3 | IsRightBoundaryEdge w e} ∩
        {w | edgeWest w e = v ∨ edgeEast w e = v}) := by
    ext w
    simp [IsCutVertex, OnLeftBoundary, OnRightBoundary]
  rw [this]
  exact (MeasurableSet.iUnion (fun e => (measurableSet_leftBoundaryEdge e).inter
    (measurableSet_endpoint e v))).inter
    (MeasurableSet.iUnion (fun e => (measurableSet_rightBoundaryEdge e).inter
      (measurableSet_endpoint e v)))

/-- Measurability of the infinite-cut-vertex event
`{w | {v | IsCutVertex w v}.Infinite}` (`prop-cut-vertex`, -/
theorem measurableSet_infinite_cutVertices :
    MeasurableSet {w : ℕ → Fin 3 | {v : ℕ | IsCutVertex w v}.Infinite} := by
  have : {w : ℕ → Fin 3 | {v : ℕ | IsCutVertex w v}.Infinite} =
      ⋂ N : ℕ, ⋃ v : ℕ, ⋃ (_ : N ≤ v), {w : ℕ → Fin 3 | IsCutVertex w v} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    exact infinite_iff_forall_exists_ge _
  rw [this]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun v => MeasurableSet.iUnion
    (fun _ => measurableSet_isCutVertex v)))

private theorem integrateCodes_congr {c c' : ℕ → Fin 3} {n : ℕ} (h : ∀ i < n, c i = c' i) :
    integrateCodes c n = integrateCodes c' n := by
  unfold integrateCodes
  exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])

/-- `pitmanCode` is measurable on code space: coordinate `i` of the flip depends only on -/
theorem measurable_pitmanCode : Measurable (pitmanCode : (ℕ → Fin 3) → ℕ → Fin 3) := by
  rw [measurable_pi_iff]
  intro i
  refine measurable_of_factors_prefix (i + 1) _ (fun c c' h => ?_)
  unfold pitmanCode
  have hI : ∀ j ≤ i + 1, integrateCodes c j = integrateCodes c' j :=
    fun j hj => integrateCodes_congr (fun k hk => h k (by omega))
  have hcond : (∀ j ≤ i, (integrateCodes c (i + 1)).1 < (integrateCodes c j).1) ↔
      (∀ j ≤ i, (integrateCodes c' (i + 1)).1 < (integrateCodes c' j).1) := by
    rw [hI (i + 1) le_rfl]
    exact forall_congr' (fun j => forall_congr' (fun hj => by rw [hI j (by omega)]))
  rw [h i (by omega)]
  simp only [hcond]

/-- The shifted code map `ω ↦ pitmanCode (fun i => ω (i + 1))` used in the coupling is
measurable (SA43 caveat). -/
theorem measurable_pitmanCode_shift :
    Measurable (fun ω : ℕ → Fin 3 => pitmanCode (fun i => ω (i + 1))) := by
  have hs : Measurable (fun (ω : ℕ → Fin 3) (i : ℕ) => ω (i + 1)) := by fun_prop
  exact measurable_pitmanCode.comp hs

/-- Preimages under the coupling code map of measurable events are measurable in `ω`
(SA43 caveat; applies to every event of this file). -/
theorem measurableSet_preimage_pitmanCode_shift {E : Set (ℕ → Fin 3)}
    (hE : MeasurableSet E) :
    MeasurableSet {ω : ℕ → Fin 3 | pitmanCode (fun i => ω (i + 1)) ∈ E} :=
  measurable_pitmanCode_shift hE

end DirectedDistances.KMSW
