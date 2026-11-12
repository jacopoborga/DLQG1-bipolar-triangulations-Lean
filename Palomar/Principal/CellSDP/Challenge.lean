/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.NormNum
/-!
# Shortest directed paths in a finite KMSW cell (Theorem 1.13)

One constant A(delta)>1 works for every positive number n of exploration steps.
Under the genuine uniform independent code law, the same event contains both
lower-to-upper boundary shortest-path bounds and a right lower-boundary vertex
at shortest distance at least A inverse times n^(3/8) from the root source.
Boundary hitting witnesses are conclusions inside the event, not assumptions.
The code at time zero is deterministic; the source steps use omega(i+1).
The stage retains every geometric edge ID, including missing boundary edges;
only allocated present edges are directed arrows. Parallel arrows stay distinct.
-/
public section
section WalkSource
namespace DirectedDistances.KMSW
/-- The three KMSW moves, in the original constructor order down, left, up. -/
inductive Step
  | down
  | left
  | up
  deriving DecidableEq
end DirectedDistances.KMSW
end WalkSource
section IncrementSource
namespace DirectedDistances.RandomWalk
/-- The three source increments (-1,0), (0,1), (1,-1), indexed by Fin3. -/
@[expose] def lazyTwoDimensionalStep (c : Fin 3) : ℤ × ℤ :=
  ((c : ℤ) - 1, if c = 0 then 0 else if c = 1 then 1 else -1)
end DirectedDistances.RandomWalk
end IncrementSource
section StageSource
namespace DirectedDistances.KMSW
open scoped BigOperators
/-- Finite KMSW bookkeeping state: allocated vertex/edge counts, geometric endpoints, present-edge
flags, triangles, active edge and four boundary lists. Arbitrary states carry no geometric
assertion. -/
structure State where
  nextVertex : ℕ
  nextEdge : ℕ
  west : ℕ → ℕ
  east : ℕ → ℕ
  present : ℕ → Bool
  triangles : List (ℕ × ℕ × ℕ)
  active : ℕ
  UL : List ℕ
  UR : List ℕ
  LL : List ℕ
  LR : List ℕ
/-- The initial root edge from vertex0 to vertex1, present and active. -/
@[expose] def kmswInit : State where
  nextVertex := 2
  nextEdge := 1
  west := fun _ => 0
  east := fun _ => 1
  present := fun _ => true
  triangles := []
  active := 0
  UL := [0]
  UR := []
  LL := []
  LR := [0]
/-- Allocate one geometric edge with its exact endpoints and presence status. -/
@[expose] def State.addEdge (s : State) (a b : ℕ) (p : Bool) : State :=
  { s with
    nextEdge := s.nextEdge + 1
    west := fun e => if e = s.nextEdge then a else s.west e
    east := fun e => if e = s.nextEdge then b else s.east e
    present := fun e => if e = s.nextEdge then p else s.present e }
/-- The existing public finite-code typing theorem: three is nonzero. -/
theorem kmswCodeStep._proof_1 :
    @NeZero ℕ (@Zero.ofOfNat0 ℕ _) ((2 : ℕ) + 1) := ⟨by decide⟩
section
attribute [local instance 1000000] kmswCodeStep._proof_1
/-- Decode each uniform Fin3 source code into its exact KMSW move. -/
@[expose] def kmswCodeStep (c : Fin 3) : Step :=
  if c = 0 then .left else if c = 1 then .up else .down
end
/-- Apply one literal KMSW move, retaining missing boundary edges and edge IDs. -/
@[expose] def kmswStepOfStep (s : State) : Step → State
  | .down =>
    match s.UR with
    | e :: es =>
      { s with
        present := fun f => if f = e then true else s.present f
        active := e
        UL := s.UL ++ [e]
        UR := es }
    | [] =>
      let t := s.addEdge (s.east s.active) s.nextVertex true
      { t with
        nextVertex := s.nextVertex + 1
        active := s.nextEdge
        UL := s.UL ++ [s.nextEdge]
        LR := s.LR ++ [s.nextEdge] }
  | .left =>
    match s.UL.dropLast.reverse with
    | e :: es =>
      let t := s.addEdge (s.west e) (s.east s.active) true
      { t with
        active := s.nextEdge
        triangles := s.triangles ++ [(s.active, s.nextEdge, e)]
        UL := es.reverse ++ [s.nextEdge] }
    | [] =>
      let t := s.addEdge s.nextVertex (s.east s.active) true
      let u := t.addEdge s.nextVertex (s.west s.active) false
      { u with
        nextVertex := s.nextVertex + 1
        active := s.nextEdge
        triangles := s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)]
        UL := [s.nextEdge]
        LL := (s.nextEdge + 1) :: s.LL }
  | .up =>
    let t := s.addEdge (s.west s.active) s.nextVertex true
    let u := t.addEdge s.nextVertex (s.east s.active) false
    { u with
      nextVertex := s.nextVertex + 1
      active := s.nextEdge
      triangles := s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)]
      UL := s.UL.dropLast ++ [s.nextEdge]
      UR := (s.nextEdge + 1) :: s.UR }
/-- Advance one finite stage using the decoded source code. -/
@[expose] def kmswStep (s : State) (c : Fin 3) : State :=
  kmswStepOfStep s (kmswCodeStep c)
/-- The finite stage after n source-code steps, recursively from the root edge. -/
@[expose] def kmswStage (w : ℕ → Fin 3) : ℕ → State
  | 0 => kmswInit
  | n + 1 => kmswStep (kmswStage w n) (w n)
end DirectedDistances.KMSW
end StageSource
section MarkovSource
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open Finset Preorder
open scoped ENNReal Classical
variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
/-- The actual countable-state Markov history kernel, reading the current state. -/
@[expose] noncomputable def markovHistoryKernel (κ : Kernel S S) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → S) S where
  toFun p := κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := measurable_of_countable _
/-- The history kernel evaluates the transition kernel at the final history state. -/
theorem markovHistoryKernel_apply (κ : Kernel S S) (n : ℕ)
    (p : (i : Finset.Iic n) → S) :
    markovHistoryKernel κ n p = κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := rfl
/-- A probability transition kernel gives a probability history kernel. -/
instance (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovHistoryKernel κ n) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure (κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
    infer_instance
/-- The full infinite Ionescu-Tulcea trajectory starting at the specified state. -/
@[expose] noncomputable def markovTrajectory (κ : Kernel S S) [IsMarkovKernel κ]
    (s : S) : Measure (ℕ → S) :=
  Kernel.traj (X := fun _ => S) (markovHistoryKernel κ) 0 (fun _ => s)
/-- The constructed infinite trajectory is a probability measure. -/
instance (κ : Kernel S S) [IsMarkovKernel κ] (s : S) :
    IsProbabilityMeasure (markovTrajectory κ s) := by
  unfold markovTrajectory
  infer_instance
end DirectedDistances.Probability
end MarkovSource
section IIDSource
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped BigOperators
/-- Normalization proof for the uniform probability measure on all three codes. -/
private instance : IsProbabilityMeasure
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)
/-- The literal uniform probability law on the three source codes. -/
@[expose] noncomputable def uniformCodeMeasure : Measure (Fin 3) :=
  Measure.uniformOfFinset Finset.univ
/-- The uniform source-code law has total mass1. -/
instance : IsProbabilityMeasure uniformCodeMeasure := by
  unfold uniformCodeMeasure
  infer_instance
/-- The existing public IID time-zero numeral typing theorem: three is nonzero. -/
theorem iidCodeMeasure._proof_4 :
    @NeZero ℕ (@Zero.ofOfNat0 ℕ _) ((2 : ℕ) + 1) := ⟨by decide⟩
section
attribute [local instance 1000000] iidCodeMeasure._proof_4
/-- The genuine independent code trajectory, with time-zero state0 and uniform future transitions. -/
@[expose] noncomputable def iidCodeMeasure : Measure (ℕ → Fin 3) :=
  DirectedDistances.Probability.markovTrajectory (Kernel.const (Fin 3) uniformCodeMeasure) 0
end
/-- The independent source-code trajectory has total mass1. -/
instance : IsProbabilityMeasure iidCodeMeasure := by
  unfold iidCodeMeasure
  infer_instance
end DirectedDistances.RandomWalk
end IIDSource
@[expose] public section StageGraphSource
namespace DirectedDistances.KMSW
open Quiver
/-- A vertex ID in the stage quiver; source upper bounds restrict to allocated IDs. -/
structure StagePresentVertex (w : ℕ → Fin 3) (n : ℕ) where
  id : ℕ
  deriving DecidableEq
/-- One directed arrow per allocated present edge ID with the stage endpoints. -/
instance stagePresentQuiver (w : ℕ → Fin 3) (n : ℕ) :
    Quiver (StagePresentVertex w n) where
  Hom u v := {e : ℕ // e < (kmswStage w n).nextEdge ∧
    (kmswStage w n).present e = true ∧
    (kmswStage w n).west e = u.id ∧ (kmswStage w n).east e = v.id}
end DirectedDistances.KMSW
end StageGraphSource
section DistanceSource
@[expose] public section
namespace DirectedDistances
open Quiver
universe u v
variable {V : Type u} [Quiver.{v} V] {a b c : V}
/-- The infimum of all directed path lengths in ENat; unreachable pairs have infinity. -/
noncomputable def sdp (a b : V) : ℕ∞ :=
  ⨅ p : Path a b, (p.length : ℕ∞)
end DirectedDistances
end
end DistanceSource
section BoundaryCoordinatesSource
namespace DirectedDistances.KMSW
open scoped BigOperators
/-- The accumulated horizontal coordinate of the literal KMSW source steps. -/
@[expose] def L (w : ℕ → Fin 3) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (RandomWalk.lazyTwoDimensionalStep (w i)).1
/-- The accumulated vertical coordinate of the literal KMSW source steps. -/
@[expose] def R (w : ℕ → Fin 3) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (RandomWalk.lazyTwoDimensionalStep (w i)).2
end DirectedDistances.KMSW
end BoundaryCoordinatesSource
section BoundaryActSource
namespace DirectedDistances.KMSW
open scoped Classical
/-- The active geometric edge ID at the specified finite stage. -/
@[expose] def act (w : ℕ → Fin 3) (m : ℕ) : ℕ := (kmswStage w m).active
end DirectedDistances.KMSW
end BoundaryActSource
section BoundaryStableSource
namespace DirectedDistances.KMSW
/-- The stable west endpoint, read at stage e where edge e is already allocated. -/
@[expose] def edgeWest (w : ℕ → Fin 3) (e : ℕ) : ℕ := (kmswStage w e).west e
/-- The actual stable west endpoint of the active edge. -/
@[expose] def activeInitial (w : ℕ → Fin 3) (n : ℕ) : ℕ := edgeWest w (act w n)
end DirectedDistances.KMSW
end BoundaryStableSource
section BoundaryHitSource
namespace DirectedDistances.KMSW
open scoped Classical
/-- Actual hits of every required coordinate level. These witnesses are existential conclusions
inside the probability event. -/
structure BoundaryHitWitnesses (w : ℕ → Fin 3) : Prop where
  rightHit : ∀ k : ℤ, 1 ≤ k → ∃ n, R w n = -k
  leftHit : ∀ k : ℤ, k ≤ -1 → ∃ n, L w n = k
/-- The first hit of the required coordinate level, using its actual existence witness. -/
@[expose] noncomputable def boundaryHitTime (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ := by
  classical
  by_cases hk0 : k = 0
  · exact 0
  · by_cases hkpos : 0 < k
    · exact Nat.find (h.rightHit k (by omega))
    · exact Nat.find (h.leftHit k (by omega))
/-- The hit-indexed boundary vertex, with x0=0 and x1=1 exactly. -/
@[expose] noncomputable def boundaryVertex (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ := by
  classical
  by_cases hk0 : k = 0
  · exact 0
  · by_cases hk1 : k = 1
    · exact 1
    · exact activeInitial w (boundaryHitTime w h k)
end DirectedDistances.KMSW
end BoundaryHitSource
namespace DLQG1.Palomar.Principal
open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances DirectedDistances.KMSW DirectedDistances.RandomWalk
/-- Theorem 1.13: all three boundary-distance clauses in one shared-constant event. -/
theorem cell_sdp (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ n : ℕ, 1 ≤ n →
      1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
        let w := fun i => ω (i + 1)
        (∀ x : ℕ,
          (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
            (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
          ∃ y : ℕ,
            (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
              (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
            sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
              (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)) ∧
        (∀ y : ℕ,
          (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
            (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
          ∃ x : ℕ,
            (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
              (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
            sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
              (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)) ∧
        (∃ h : BoundaryHitWitnesses w, ∃ r : ℕ, 1 ≤ r ∧
          (∃ e ∈ (kmswStage w n).LR,
            (kmswStage w n).west e = boundaryVertex w h (r : ℤ) ∨
              (kmswStage w n).east e = boundaryVertex w h (r : ℤ)) ∧
          A⁻¹ * (n : ℝ) ^ (3 / 8 : ℝ) ≤
            ((sdp (⟨boundaryVertex w h 0⟩ : StagePresentVertex w n)
              ⟨boundaryVertex w h (r : ℤ)⟩).toNat : ℝ))} := by
  sorry
end DLQG1.Palomar.Principal
