module

public import DirectedDistances.KMSW.CutEquivalence
public import DirectedDistances.KMSW.WholePlaneLemma38IntegerStart
import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Infinite-stage KMSW boundary membership -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Definition 3.2: an edge belongs to the limiting boundary
selected by `B` when it belongs to that side at infinitely many KMSW stages -/
@[expose] def kmswBoundaryLimsup (B : State → List ℕ) (w : ℕ → Fin 3)
    (e : ℕ) : Prop :=
  {j : ℕ | e ∈ B (kmswStage w j)}.Infinite

/-- Helper toward Definition 3.2: infinite-stage membership is equivalent to -/
theorem kmswBoundaryLimsup_iff_forall_exists_ge
    (B : State → List ℕ) (w : ℕ → Fin 3) (e : ℕ) :
    kmswBoundaryLimsup B w e ↔
      ∀ N, ∃ j, N ≤ j ∧ e ∈ B (kmswStage w j) := by
  change Set.Infinite {j : ℕ | e ∈ B (kmswStage w j)} ↔ _
  rw [← Nat.frequently_atTop_iff_infinite]
  exact Filter.frequently_atTop

/-- Helper toward Definition 3.2: the limiting boundary is the `atTop` -/
theorem kmswBoundaryLimsup_iff_frequently
    (B : State → List ℕ) (w : ℕ → Fin 3) (e : ℕ) :
    kmswBoundaryLimsup B w e ↔
      ∃ᶠ j in Filter.atTop, e ∈ B (kmswStage w j) := by
  change Set.Infinite {j : ℕ | e ∈ B (kmswStage w j)} ↔ _
  exact (Nat.frequently_atTop_iff_infinite (p := fun j =>
    e ∈ B (kmswStage w j))).symm

/-- Helper toward Definition 3.2: for the upper-left selector, limiting
membership is the existing semi-infinite upper-left predicate
transience or endpoint hypotheses. -/
theorem kmswBoundaryLimsup_iff_isLeftBoundaryEdge
    (w : ℕ → Fin 3) (e : ℕ) :
    kmswBoundaryLimsup State.UL w e ↔ IsLeftBoundaryEdge w e := Iff.rfl

/-- Helper toward Definition 3.2: for the lower-right selector, limiting
membership is the existing semi-infinite lower-right predicate
transience or endpoint hypotheses. -/
theorem kmswBoundaryLimsup_iff_isRightBoundaryEdge
    (w : ℕ → Fin 3) (e : ℕ) :
    kmswBoundaryLimsup State.LR w e ↔ IsRightBoundaryEdge w e := Iff.rfl

/-- Helper toward Definition 3.2: a whole-plane edge is in the limiting
boundary when infinitely many integer-start runs see a run edge mapping to it
that belongs to the selected semi-infinite boundary -/
@[expose] def kmswBiInfiniteBoundaryLimsup (B : State → List ℕ)
    (W : ℤ → Fin 3) (e : WholePlaneEdge W) : Prop :=
  ∃ᶠ n in Filter.atBot,
    ∃ f : ℕ, lemma38StartEdgeι W n f = e ∧
      kmswBoundaryLimsup B (lemma38StartStream W n) f

/-- Helper toward Definition 3.2: bi-infinite boundary membership is witnessed
by such a run from arbitrarily negative starts -/
theorem kmswBiInfiniteBoundaryLimsup_iff_forall_exists_le
    (B : State → List ℕ) (W : ℤ → Fin 3) (e : WholePlaneEdge W) :
    kmswBiInfiniteBoundaryLimsup B W e ↔
      ∀ N : ℤ, ∃ n, n ≤ N ∧ ∃ f : ℕ,
        lemma38StartEdgeι W n f = e ∧
          kmswBoundaryLimsup B (lemma38StartStream W n) f := by
  change (∃ᶠ n in Filter.atBot,
    ∃ f : ℕ, lemma38StartEdgeι W n f = e ∧
      kmswBoundaryLimsup B (lemma38StartStream W n) f) ↔ _
  exact Filter.frequently_atBot

end DirectedDistances.KMSW
