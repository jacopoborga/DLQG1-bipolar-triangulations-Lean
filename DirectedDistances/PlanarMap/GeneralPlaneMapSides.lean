/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import DirectedDistances.PlanarMap.GeneralPlaneMap

/-! # Winding-based sides in a general plane map

side predicates use chord loops and winding number. Jordan-curve, uniqueness
of a left face, and agreement with the PL-wedge convention remain separate
compatibility obligations. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology ComplexConjugate

variable {V E : Type*}

/-- Helper toward Definition 3.2: a loop has winding number `n` about `w` when
its translate by `-w` admits a continuous logarithm whose endpoint increment
is `2 * π * I * n`. This formulation uses an existential lift, with no
choice of argument function. -/
@[expose]
def HasWinding {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ) : Prop :=
  ∃ φ : C(unitInterval, ℂ),
    (∀ t, Complex.exp (φ t) = L t - w) ∧
      φ 1 - φ 0 = 2 * Real.pi * Complex.I * n

/-- Helper toward Definition 3.2: orient a present edge according to the
carrier's `forward` field. -/
@[expose]
def orientedArc (M : DirectedPlaneMapWithMissing V E)
    (e : {e : E // ¬ M.toPlaneMapWithMissing.missing e}) :
    Path
      (M.toPlaneMapWithMissing.pos (M.tail e))
      (M.toPlaneMapWithMissing.pos (M.head e)) := by
  by_cases h : M.forward e
  · simpa [DirectedPlaneMapWithMissing.tail,
      DirectedPlaneMapWithMissing.head, h] using
        M.toPlaneMapWithMissing.arc e.1
  · simpa [DirectedPlaneMapWithMissing.tail,
      DirectedPlaneMapWithMissing.head, h] using
        (M.toPlaneMapWithMissing.arc e.1).symm

/-- Helper toward Definition 3.2: the parameterized arc between two points of
an oriented edge. `truncateOfLE` has the same directed image as the usual
subpath; its constant pauses only reparameterize the traversal. -/
@[expose]
def edgeSubarc {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) (a b : I) (hab : a ≤ b) : Path (γ a) (γ b) :=
  (γ.truncateOfLE (t₀ := (a : ℝ)) (t₁ := (b : ℝ)) (by exact hab)).cast
    (γ.extend_extends' a).symm (γ.extend_extends' b).symm

abbrev PresentEdge (M : DirectedPlaneMapWithMissing V E) :=
  {e : E // ¬ M.toPlaneMapWithMissing.missing e}

abbrev Drawing (M : DirectedPlaneMapWithMissing V E) :=
  M.toPlaneMapWithMissing.toPlaneGraphDrawing

/-- Helper toward Definition 3.2: along an oriented path `γ`, the set `F`
touches the left side at `s` when a chord in `F` closes a positively wound
loop and points of `F` with that winding accumulate at `γ s`. -/
@[expose]
def LeftAtOn {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s : {t : I // t ∈ openParams}) : Prop :=
  ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b) (_hb : b < 1),
    ∃ q : Path (γ b) (γ a),
      Function.Injective q ∧
      (∀ t : I, t ∈ openParams → q t ∈ F) ∧
      γ s.1 ∈ closure
        {w : ℂ | w ∈ F ∧
          HasWinding
            ((edgeSubarc γ a b (le_of_lt (lt_trans _has _hsb))).trans q)
            w 1}

/-- Helper toward Definition 3.2: along an oriented path `γ`, the set `F`
touches the right side at `s` when the chord loop in `LeftAtOn` has winding
number `-1`. -/
@[expose]
def RightAtOn {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s : {t : I // t ∈ openParams}) : Prop :=
  ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b) (_hb : b < 1),
    ∃ q : Path (γ b) (γ a),
      Function.Injective q ∧
      (∀ t : I, t ∈ openParams → q t ∈ F) ∧
      γ s.1 ∈ closure
        {w : ℂ | w ∈ F ∧
          HasWinding
            ((edgeSubarc γ a b (le_of_lt (lt_trans _has _hsb))).trans q)
            w (-1)}

/-- Helper toward Definition 3.2: the external face `F` touches the left side
of the oriented edge at `s` when a chord inside `F` closes a positively wound
loop and points of `F` with that winding accumulate at the edge point. -/
@[expose]
def LeftAt (M : DirectedPlaneMapWithMissing V E)
    (F : PlaneGraphDrawing.Face (Drawing M))
    (e : PresentEdge M) (s : {t : I // t ∈ openParams}) : Prop :=
  LeftAtOn F.1 (orientedArc M e) s

/-- Helper toward Definition 3.2: right-side touching uses winding number
`-1` in the chord loop of `LeftAt`. -/
@[expose]
def RightAt (M : DirectedPlaneMapWithMissing V E)
    (F : PlaneGraphDrawing.Face (Drawing M))
    (e : PresentEdge M) (s : {t : I // t ∈ openParams}) : Prop :=
  RightAtOn F.1 (orientedArc M e) s

/-- Helper toward Definition 3.2: a face lies on the left along the entire
open oriented edge. -/
@[expose]
def LeftOf (M : DirectedPlaneMapWithMissing V E)
    (F : PlaneGraphDrawing.Face (Drawing M))
    (e : PresentEdge M) : Prop := ∀ s, LeftAt M F e s

/-- Helper toward Definition 3.2: a face lies on the right along the entire
open oriented edge. -/
@[expose]
def RightOf (M : DirectedPlaneMapWithMissing V E)
    (F : PlaneGraphDrawing.Face (Drawing M))
    (e : PresentEdge M) : Prop := ∀ s, RightAt M F e s

/-- Helper toward Definition 3.2: the upper-left edge set consists of present
edges with some external face on their left. -/
@[expose]
def UL (M : DirectedPlaneMapWithMissing V E) : Set (PresentEdge M) :=
  {e | ∃ F : PlaneGraphDrawing.Face (Drawing M),
    (Drawing M).IsExternal F ∧ LeftOf M F e}

/-- Helper toward Definition 3.2: the lower-right edge set consists of present
edges with some external face on their right. -/
@[expose]
def LR (M : DirectedPlaneMapWithMissing V E) : Set (PresentEdge M) :=
  {e | ∃ F : PlaneGraphDrawing.Face (Drawing M),
    (Drawing M).IsExternal F ∧ RightOf M F e}

/-- Helper toward Definition 3.2: conjugation of the loop and base point
negates its winding number. -/
theorem hasWinding_conj {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ)
    (h : HasWinding L w n) :
    HasWinding (L.map Complex.continuous_conj) (conj w) (-n) := by
  obtain ⟨φ, hφ, hinc⟩ := h
  refine ⟨(⟨starRingEnd ℂ, Complex.continuous_conj⟩ : C(ℂ, ℂ)).comp φ, ?_, ?_⟩
  · intro t
    change Complex.exp (conj (φ t)) = conj (L t) - conj w
    rw [Complex.exp_conj, hφ]
    simp
  · change conj (φ 1) - conj (φ 0) = _
    calc
      conj (φ 1) - conj (φ 0) = conj (φ 1 - φ 0) := by rw [← map_sub]
      _ = conj (2 * Real.pi * Complex.I * n) := congrArg conj hinc
      _ = 2 * Real.pi * Complex.I * (-(n : ℂ)) := by
        simp only [map_mul, map_ofNat, map_intCast, Complex.conj_ofReal,
          Complex.conj_I]
        ring
      _ = 2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) :=
        congrArg (fun x : ℂ => 2 * Real.pi * Complex.I * x)
          (Int.cast_neg n).symm

/-- Helper toward Definition 3.2: the expected reversal law is recorded as a
compatibility obligation. It is not assumed by either side definition. -/
@[expose]
def leftAt_reversal_statement : Prop :=
  ∀ (M : DirectedPlaneMapWithMissing V E)
    (F : PlaneGraphDrawing.Face (Drawing M))
    (e : PresentEdge M) (s s' : {t : I // t ∈ openParams}),
    (s'.1 : ℝ) + (s.1 : ℝ) = 1 →
    LeftAtOn F.1 (orientedArc M e).symm s' ↔
      RightAtOn F.1 (orientedArc M e) s

/-! The Jordan-curve theorem, uniqueness of a left face, and agreement of the
winding side test with the locally finite PL-wedge convention are separate
compatibility obligations. The reversal statement above likewise remains to
be proved; none is a premise of these definitions. -/

end DirectedDistances.PlanarMap

