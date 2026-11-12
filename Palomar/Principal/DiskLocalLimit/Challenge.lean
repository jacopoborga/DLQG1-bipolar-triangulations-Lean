module
public meta import Lean.Elab.PreDefinition.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Order.KonigLemma
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Order.Cadlag
/-! Proposition 5.16: finite disk sampling and its geometric-law limit.
Ordinary geometric and sampling definitions are fully compared.
The 36 named construction/result proof holes are quarantined; Solutions provide complete proofs. -/
noncomputable section
namespace DirectedDistances.PaperProofs.Section5
end DirectedDistances.PaperProofs.Section5
namespace DirectedDistances.KMSW.WholePlanePastGlueData
end DirectedDistances.KMSW.WholePlanePastGlueData
public section
namespace DirectedDistances.KMSW
inductive Step
  | down
  | left
  | up
  deriving DecidableEq
end DirectedDistances.KMSW
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
@[expose] def lazyTwoDimensionalStep (c : Fin 3) : ℤ × ℤ := ((c : ℤ) - 1, if c = 0 then 0 else if c = 1 then 1 else -1)
end DirectedDistances.RandomWalk
namespace DirectedDistances.KMSW
open scoped BigOperators
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
@[expose] def State.addEdge (s : State) (a b : ℕ) (p : Bool) : State :=
  { s with
    nextEdge := s.nextEdge + 1
    west := fun e => if e = s.nextEdge then a else s.west e
    east := fun e => if e = s.nextEdge then b else s.east e
    present := fun e => if e = s.nextEdge then p else s.present e }
theorem kmswCodeStep._proof_1 : @NeZero ℕ (@Zero.ofOfNat0 ℕ _) ((2 : ℕ) + 1) := ⟨by decide⟩
section
attribute [local instance 1000000] kmswCodeStep._proof_1
@[expose] def kmswCodeStep (c : Fin 3) : Step := if c = 0 then .left else if c = 1 then .up else .down
end
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
@[expose] def kmswStep (s : State) (c : Fin 3) : State := kmswStepOfStep s (kmswCodeStep c)
@[expose] def kmswStage (w : ℕ → Fin 3) : ℕ → State
  | 0 => kmswInit
  | n + 1 => kmswStep (kmswStage w n) (w n)
@[expose] def L (w : ℕ → Fin 3) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, (RandomWalk.lazyTwoDimensionalStep (w i)).1
open scoped Classical
@[expose] def kmswLLCreatedEdge (w : ℕ → Fin 3) (m : ℕ) : ℕ := (kmswStage w m).nextEdge - 1
@[expose] def act (w : ℕ → Fin 3) (m : ℕ) : ℕ := (kmswStage w m).active
theorem act_lt_nextEdge (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) : act w m < (kmswStage w n).nextEdge := by sorry
end DirectedDistances.KMSW
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal Classical
variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
@[expose] noncomputable def markovHistoryKernel (κ : Kernel S S) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → S) S where
  toFun p := κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := measurable_of_countable _
instance (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovHistoryKernel κ n) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure (κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
    infer_instance
@[expose] noncomputable def markovTrajectory (κ : Kernel S S) [IsMarkovKernel κ] (s : S) : Measure (ℕ → S) := Kernel.traj (X := fun _ => S) (markovHistoryKernel κ) 0 (fun _ => s)
instance (κ : Kernel S S) [IsMarkovKernel κ] (s : S) :
    IsProbabilityMeasure (markovTrajectory κ s) := by
  unfold markovTrajectory
  infer_instance
end DirectedDistances.Probability
namespace DirectedDistances.KMSW
open scoped Classical
@[expose] def edgeWest (w : ℕ → Fin 3) (e : ℕ) : ℕ := (kmswStage w e).west e
@[expose] def edgeEast (w : ℕ → Fin 3) (e : ℕ) : ℕ := (kmswStage w e).east e
open Quiver
def EdgePresent (w : ℕ → Fin 3) (e : ℕ) : Prop := ∃ n, e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true
end DirectedDistances.KMSW
namespace DirectedDistances.PlanarMap
open Equiv
universe u
variable {D : Type u} [DecidableEq D]
@[expose] def insertAfter (σ : Equiv.Perm D) (a x : D) : Equiv.Perm D := σ * Equiv.swap a x
@[expose] def insertBefore (σ : Equiv.Perm D) (a x : D) : Equiv.Perm D := Equiv.swap a x * σ
end DirectedDistances.PlanarMap
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap
abbrev StageDart (k : ℕ) := Fin k × Bool
@[expose] def stageEndpoint (s : State) (d : StageDart s.nextEdge) : ℕ := if d.2 then s.east d.1.val else s.west d.1.val
namespace StageRotation
@[expose] def allocation (k r : ℕ) : StageDart k ⊕ StageDart r ≃ StageDart (k + r) where
  toFun
    | .inl (e, b) => (⟨e.val, by omega⟩, b)
    | .inr (e, b) => (⟨k + e.val, by omega⟩, b)
  invFun d := if h : d.1.val < k then .inl (⟨d.1.val, h⟩, d.2)
    else .inr (⟨d.1.val - k, by have := d.1.isLt; omega⟩, d.2)
  left_inv := by
    rintro (⟨e, b⟩ | ⟨e, b⟩)
    · simp only [e.isLt, ↓reduceDIte]
    · simp only [show ¬ k + e.val < k by omega, ↓reduceDIte]
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Fin.ext
        dsimp only
        omega
      · rfl
  right_inv := by
    rintro ⟨e, b⟩
    dsimp only
    by_cases h : e.val < k
    · simp only [h, ↓reduceDIte]
    · simp only [h, ↓reduceDIte]
      apply Prod.ext
      · apply Fin.ext
        dsimp only
        omega
      · rfl
@[expose] def pairSplice {D F : Type*} [DecidableEq D] [DecidableEq F] (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F) : Equiv.Perm (D ⊕ F) := insertBefore (insertAfter (Equiv.sumCongr σ τ) (.inl a) (.inr x))
    (.inl b) (.inr y)
@[expose] def pendant (k : ℕ) (σ : Equiv.Perm (StageDart k)) (A : StageDart k) : Equiv.Perm (StageDart (k + 1)) := (allocation k 1).permCongr (insertBefore (Equiv.sumCongr σ (Equiv.refl _)) (.inl A) (.inr (0, false)))
@[expose] def leftExisting (k : ℕ) (σ : Equiv.Perm (StageDart k)) (e A : StageDart k) : Equiv.Perm (StageDart (k + 1)) := (allocation k 1).permCongr (pairSplice σ (Equiv.refl _) e A (0, false) (0, true))
@[expose] def leftFresh (k : ℕ) (σ : Equiv.Perm (StageDart k)) (a A : StageDart k) : Equiv.Perm (StageDart (k + 2)) := (allocation k 2).permCongr (pairSplice σ (Equiv.swap (0, false) (1, false)) a A (1, true) (0, true))
@[expose] def up (k : ℕ) (σ : Equiv.Perm (StageDart k)) (a A : StageDart k) : Equiv.Perm (StageDart (k + 2)) := (allocation k 2).permCongr (pairSplice σ (Equiv.swap (0, true) (1, false)) a A (0, false) (1, true))
@[expose] def resize {k l : ℕ} (h : k = l) (σ : Equiv.Perm (StageDart k)) : Equiv.Perm (StageDart l) := h ▸ σ
theorem step._proof_5 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .down) (hr : s.UR = []) : s.nextEdge + 1 = (kmswStep s c).nextEdge := by simp only [kmswStep, hc, kmswStepOfStep, hr, State.addEdge]
theorem step._proof_6 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .down) (head : ℕ) (tail : List ℕ) (hr : s.UR = head :: tail) : s.nextEdge = (kmswStep s c).nextEdge := by simp only [kmswStep, hc, kmswStepOfStep, hr]
theorem step._proof_7 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .left) (hl : s.UL.dropLast.reverse = []) : s.nextEdge + 2 = (kmswStep s c).nextEdge := by simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
theorem step._proof_9 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .left) (e : ℕ) (es : List ℕ) (hl : s.UL.dropLast.reverse = e :: es) : s.nextEdge + 1 = (kmswStep s c).nextEdge := by simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
theorem step._proof_10 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .up) : s.nextEdge + 2 = (kmswStep s c).nextEdge := by simp only [kmswStep, hc, kmswStepOfStep, State.addEdge]
@[expose] def step (s : State) (ha : s.active < s.nextEdge)
    (hu : ∀ e ∈ s.UL, e < s.nextEdge) (σ : Equiv.Perm (StageDart s.nextEdge))
    (c : Fin 3) : Equiv.Perm (StageDart (kmswStep s c).nextEdge) :=
  match hc : kmswCodeStep c with
  | .down => match hr : s.UR with
    | [] => resize (DirectedDistances.KMSW.StageRotation.step._proof_5 s c hc hr)
        (pendant s.nextEdge σ (⟨s.active, ha⟩, true))
    | head :: tail => resize (DirectedDistances.KMSW.StageRotation.step._proof_6 s c hc head tail hr) σ
  | .left => match hl : s.UL.dropLast.reverse with
    | [] => resize (DirectedDistances.KMSW.StageRotation.step._proof_7 s c hc hl)
        (leftFresh s.nextEdge σ (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true))
    | e :: es =>
      have he : e < s.nextEdge := hu e (List.dropLast_subset _
        (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self)))
      resize (DirectedDistances.KMSW.StageRotation.step._proof_9 s c hc e es hl)
        (leftExisting s.nextEdge σ (⟨e, he⟩, false) (⟨s.active, ha⟩, true))
  | .up => resize (DirectedDistances.KMSW.StageRotation.step._proof_10 s c hc)
      (up s.nextEdge σ (⟨s.active, ha⟩, false) (⟨s.active, ha⟩, true))
end StageRotation
theorem stageRotation_UL_bound (w : ℕ → Fin 3) (n : ℕ) : ∀ e ∈ (kmswStage w n).UL, e < (kmswStage w n).nextEdge := by sorry
@[expose] def kmswVertexComplete (w : ℕ → Fin 3) (n u : ℕ) : Prop := ∀ e, edgeWest w e = u ∨ edgeEast w e = u → e < (kmswStage w n).nextEdge
end DirectedDistances.KMSW
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped BigOperators
@[expose] noncomputable def uniformCodeMeasure : Measure (Fin 3) := Measure.uniformOfFinset Finset.univ
theorem iidCodeMeasure._proof_4 : @NeZero ℕ (@Zero.ofOfNat0 ℕ _) ((2 : ℕ) + 1) := ⟨by decide⟩
section
attribute [local instance 1000000] iidCodeMeasure._proof_4
instance : IsProbabilityMeasure uniformCodeMeasure := by
  unfold uniformCodeMeasure
  constructor
  rw [Measure.uniformOfFinset_apply]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)
@[expose] noncomputable def iidCodeMeasure : Measure (ℕ → Fin 3) := DirectedDistances.Probability.markovTrajectory (Kernel.const (Fin 3) uniformCodeMeasure) 0
@[expose] def codeWalk (ω : ℕ → Fin 3) (n : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range n, lazyTwoDimensionalStep (ω (i + 1))
@[expose] noncomputable def codeFstFirstHit (a : ℤ) (ω : ℕ → Fin 3) : ℕ∞ := by
  classical
  exact if h : ∃ n, (codeWalk ω n).1 = a then ((Nat.find h : ℕ) : ℕ∞) else ⊤
end
instance : IsProbabilityMeasure iidCodeMeasure := by
  unfold iidCodeMeasure
  infer_instance
end DirectedDistances.RandomWalk
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap
@[expose] def edgeFlip (k : ℕ) : Equiv.Perm (StageDart k) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl
section
universe u_1
@[expose] abbrev stageRot.match_1 (motive : ℕ → Sort u_1) (n : ℕ) (h0 : Unit → motive 0) (hs : ∀ n : ℕ, motive (Nat.succ n)) : motive n :=
  @Nat.casesOn (fun n => motive n) n (h0 ()) (fun n => hs n)
run_elab Lean.withExporting <| Lean.Elab.Term.withoutErrToSorry do
  let value ← Lean.Elab.Term.elabTerm (← `(fun (w : ℕ → Fin 3) (n : ℕ)
    (rec : @Nat.below (fun j => Equiv.Perm (StageDart (kmswStage w j).nextEdge)) n) =>
    stageRot.match_1 (fun n => @Nat.below (fun j => Equiv.Perm (StageDart (kmswStage w j).nextEdge)) n → Equiv.Perm (StageDart (kmswStage w n).nextEdge)) n
      (fun (_ : Unit) (_ : @Nat.below (fun j => Equiv.Perm (StageDart (kmswStage w j).nextEdge)) 0) => (1 : Equiv.Perm (StageDart (kmswStage w 0).nextEdge)))
      (fun n rec => StageRotation.step (kmswStage w n) (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) rec.1 (w n)) rec)) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let value ← Lean.instantiateMVars value
  let value ← Lean.Meta.deltaExpand value (· == ``PProd.fst)
  let type ← Lean.Meta.inferType value
  Lean.Elab.addNonRec (← Lean.getLCtx, ← Lean.Meta.getLocalInstances)
    { ref := ← Lean.getRef, kind := .abbrev, levelParams := [], modifiers := { visibility := .public, computeKind := .noncomputable, isUnsafe := false }, declName := `DirectedDistances.KMSW.stageRot._f,
      binders := .missing, numSectionVars := 0, type := type, value := value, termination := default } (abstractProofs := false)
@[expose] def stageRot (w : ℕ → Fin 3) (n : ℕ) : Equiv.Perm (StageDart (kmswStage w n).nextEdge) :=
  @Nat.brecOn (fun n => Equiv.Perm (StageDart (kmswStage w n).nextEdge)) n (stageRot._f w)
end
theorem kmswStage_endpoints_lt_nextVertex (w : ℕ → Fin 3) (n e : ℕ) (he : e < (kmswStage w n).nextEdge) : (kmswStage w n).west e < (kmswStage w n).nextVertex ∧ (kmswStage w n).east e < (kmswStage w n).nextVertex := by sorry
end DirectedDistances.KMSW
namespace DirectedDistances.RandomWalk
@[expose] def integrateCodes (c : ℕ → Fin 3) (n : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range n, lazyTwoDimensionalStep (c i)
end DirectedDistances.RandomWalk
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open scoped BigOperators
theorem finiteCodeExtend._proof_1 : @NeZero ℕ (@Zero.ofOfNat0 ℕ _) ((2 : ℕ) + 1) := @Nat.instNeZeroSucc 2
section
attribute [local instance 1000000] finiteCodeExtend._proof_1
@[expose] def finiteCodeExtend {n : ℕ} (c : Fin (n - 1) → Fin 3) : ℕ → Fin 3 := fun i => if h : i < n - 1 then c ⟨i, h⟩ else 0
end
open DirectedDistances.RandomWalk
@[expose] def KMSWLeftWalkAdmissible (ℓ n : ℕ) (c : Fin n → Fin 3) : Prop := ((ℓ : ℤ) - 1, 0) + integrateCodes (finiteCodeExtend (n := n + 1) c) n = (0, 0) ∧ ∀ k ∈ Finset.range (n + 1), 0 ≤ (((ℓ : ℤ) - 1, 0) +
    integrateCodes (finiteCodeExtend (n := n + 1) c) k).1 ∧ 0 ≤ (((ℓ : ℤ) - 1, 0) + integrateCodes (finiteCodeExtend (n := n + 1) c) k).2
instance instDecidableKMSWLeftWalkAdmissible (ℓ n : ℕ) : DecidablePred (KMSWLeftWalkAdmissible ℓ n) := by
  intro c
  unfold KMSWLeftWalkAdmissible
  infer_instance
@[expose] def KMSWLeftWalkClass (ℓ n : ℕ) := {c : Fin n → Fin 3 // KMSWLeftWalkAdmissible ℓ n c}
instance instFintypeKMSWLeftWalkClass (ℓ n : ℕ) : Fintype (KMSWLeftWalkClass ℓ n) := by
  change Fintype {c : Fin n → Fin 3 // KMSWLeftWalkAdmissible ℓ n c}
  infer_instance
end DirectedDistances.KMSW
namespace DirectedDistances.PlanarMap
structure Polyline where
  points : List ℂ
  nonempty : points ≠ []
namespace Polyline
@[expose] def start (p : Polyline) : ℂ := p.points.head p.nonempty
@[expose] def finish (p : Polyline) : ℂ := p.points.getLast p.nonempty
@[expose] def point (p : Polyline) (i : ℕ) : ℂ := p.points[i]?.getD p.start
@[expose] def segmentAt (p : Polyline) (i : ℕ) : Set ℂ := segment ℝ (p.point i) (p.point (i + 1))
@[expose] def image (p : Polyline) : Set ℂ := {p.start} ∪ {z | ∃ i, i + 1 < p.points.length ∧ z ∈ p.segmentAt i}
@[expose] def initialDirection (p : Polyline) : ℂ := p.point 1 - p.start
@[expose] def reverse (p : Polyline) : Polyline := ⟨p.points.reverse, List.reverse_ne_nil_iff.mpr p.nonempty⟩
@[expose] def IsSimple (p : Polyline) : Prop := (∀ i, i + 1 < p.points.length → p.point i ≠ p.point (i + 1)) ∧ (∀ i, i + 2 < p.points.length → p.segmentAt i ∩ p.segmentAt (i + 1) = {p.point (i + 1)}) ∧ (∀ i j, i + 1 <
    p.points.length → j + 1 < p.points.length → i + 1 < j → Disjoint (p.segmentAt i) (p.segmentAt j))
@[expose] def interior (p : Polyline) : Set ℂ := p.image \ {p.start, p.finish}
end Polyline
@[expose] def ccwTurn (a b : ℂ) : ℝ := if Complex.arg a < Complex.arg b then Complex.arg b - Complex.arg a else Complex.arg b - Complex.arg a + 2 * Real.pi
@[expose] def CcwSuccessor {D : Type*} (star : Set D) (dir : D → ℂ) (d e : D) : Prop := star.Finite ∧ d ∈ star ∧ e ∈ star ∧ ((e = d ∧ star = {d}) ∨ (e ≠ d ∧ ∀ f ∈ star, f ≠ d → ccwTurn (dir d) (dir e) ≤ ccwTurn (dir d)
    (dir f)))
structure PLDrawing (D V : Type*) (flip : D → D) (rot : Equiv.Perm D) (vert : D → V) where
  flip_involutive : Function.Involutive flip
  flip_ne : ∀ d, flip d ≠ d
  vert_rotation : ∀ d, vert (rot d) = vert d
  pos : V → ℂ
  pos_injective : Function.Injective pos
  arc : D → Polyline
  arc_simple : ∀ d, (arc d).IsSimple
  arc_length : ∀ d, 2 ≤ (arc d).points.length
  arc_start : ∀ d, (arc d).start = pos (vert d)
  arc_finish : ∀ d, (arc d).finish = pos (vert (flip d))
  arc_flip : ∀ d, arc (flip d) = (arc d).reverse
  interior_disjoint : ∀ d e, e ≠ d → e ≠ flip d → Disjoint (arc d).interior (arc e).interior
  interior_avoids_vertices : ∀ d v, pos v ∉ (arc d).interior
  locally_finite : ∀ K : Set ℂ, Bornology.IsBounded K → {d | (K ∩ (arc d).image).Nonempty}.Finite
  initial_nonzero : ∀ d, (arc d).initialDirection ≠ 0
  initial_arg_injective : ∀ d e, vert d = vert e → Complex.arg (arc d).initialDirection = Complex.arg (arc e).initialDirection → d = e
  rotation_agreement : ∀ d, CcwSuccessor {e | vert e = vert d} (fun e => (arc e).initialDirection) d (rot d)
namespace PLDrawing
variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)
@[expose] def image : Set ℂ := Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image}
@[expose] def Face := {F : Set ℂ // ∃ z, z ∉ P.image ∧ F = connectedComponentIn P.imageᶜ z}
@[expose] def IsUnbounded (F : P.Face) : Prop := ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖
@[expose] def dartBorders (d : D) (F : P.Face) : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ, 0 < t → t < δ → 0 < ε → ε < δ → (P.arc d).start + (t : ℂ) * ((P.arc d).initialDirection + (ε : ℂ) * Complex.I * (P.arc
    d).initialDirection) ∈ F.val
end PLDrawing
end DirectedDistances.PlanarMap
namespace DirectedDistances.PlanarMap
universe u
variable {D : Type u} [Fintype D] [DecidableEq D] {ℓ r a b : ℕ}
open scoped ENNReal
@[expose] noncomputable def uniformCountingMeasure (α : Type*) [Fintype α] [MeasurableSpace α] : MeasureTheory.Measure α := (Fintype.card α : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count
end DirectedDistances.PlanarMap
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap
theorem stageVertex._proof_1 (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) d < (kmswStage w n).nextVertex := by
  cases hb : d.2
  · simpa [stageEndpoint, hb] using
      (kmswStage_endpoints_lt_nextVertex w n d.1.val d.1.isLt).1
  · simpa [stageEndpoint, hb] using
      (kmswStage_endpoints_lt_nextVertex w n d.1.val d.1.isLt).2
@[expose] def stageVertex (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) : Fin (kmswStage w n).nextVertex :=
  ⟨stageEndpoint (kmswStage w n) d, stageVertex._proof_1 w n d⟩
@[expose] def StageDrawing (w : ℕ → Fin 3) (n : ℕ) := PLDrawing (StageDart (kmswStage w n).nextEdge) (Fin (kmswStage w n).nextVertex) (edgeFlip _) (stageRot w n) (stageVertex w n)
structure KMSWWindowPatchData where
  φ : ℕ → ℕ
  A : List ℕ
  B : List ℕ
  YL : List ℕ
  YR : List ℕ
  XL : List ℕ
  XR : List ℕ
@[expose] def shiftedStream (W : ℤ → Fin 3) (N : ℕ) : ℕ → Fin 3 := fun i => W ((i : ℤ) - N)
end DirectedDistances.KMSW
namespace DirectedDistances.PlanarMap
open Set unitInterval
open scoped Topology
variable {V E : Type*}
@[expose] def openParams : Set I := {t : I | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
structure PlaneGraphDrawing (V E : Type*) where
  src : E → V
  tgt : E → V
  pos : V → ℂ
  pos_injective : Function.Injective pos
  arc : (e : E) → Path (pos (src e)) (pos (tgt e))
  arc_injOn : ∀ e, Set.InjOn (arc e) openParams
  openArc_disjoint : ∀ e e', e ≠ e' → Disjoint ((arc e) '' openParams) ((arc e') '' openParams)
  openArc_avoids : ∀ e v, pos v ∉ (arc e) '' openParams
namespace PlaneGraphDrawing
variable (D : PlaneGraphDrawing V E)
@[expose] def image : Set ℂ := Set.range D.pos ∪ ⋃ e, Set.range (D.arc e)
@[expose] abbrev Face := {F : Set ℂ // ∃ z, z ∉ D.image ∧ F = connectedComponentIn D.imageᶜ z}
@[expose] def IsExternal (F : D.Face) : Prop := ¬ Bornology.IsBounded F.val
end PlaneGraphDrawing
structure PlaneMapWithMissing (V E : Type*) extends toPlaneGraphDrawing : PlaneGraphDrawing V E where
  missing : E → Prop
  missing_on_external : ∀ e, missing e → ∃ F : toPlaneGraphDrawing.Face, PlaneGraphDrawing.IsExternal toPlaneGraphDrawing F ∧ Set.range (arc e) ⊆ closure F.1
structure DirectedPlaneMapWithMissing (V E : Type*) extends toPlaneMapWithMissing : PlaneMapWithMissing V E where
  forward : {e : E // ¬ toPlaneMapWithMissing.missing e} → Bool
end DirectedDistances.PlanarMap
namespace DirectedDistances.PlanarMap
open unitInterval
open scoped Topology ComplexConjugate
variable {V E : Type*}
theorem HasWinding._proof_1 : Nat.AtLeastTwo ((1 : ℕ) + 1) := by infer_instance
section
attribute [local instance 1000000] HasWinding._proof_1
@[expose] def HasWinding {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ) : Prop := ∃ φ : C(unitInterval, ℂ), (∀ t, Complex.exp (φ t) = L t - w) ∧ φ 1 - φ 0 = 2 * Real.pi * Complex.I * n
end
@[expose] def edgeSubarc {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y) (a b : I) (hab : a ≤ b) : Path (γ a) (γ b) :=
  (γ.truncateOfLE (t₀ := (a : ℝ)) (t₁ := (b : ℝ)) (by exact hab)).cast
    (γ.extend_extends' a).symm (γ.extend_extends' b).symm
@[expose] def LeftAtOn {x y : ℂ} (F : Set ℂ) (γ : Path x y) (s : {t : I // t ∈ openParams}) : Prop := ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b) (_hb : b < 1), ∃ q : Path (γ b) (γ a), Function.Injective
    q ∧ (∀ t : I, t ∈ openParams → q t ∈ F) ∧ γ s.1 ∈ closure {w : ℂ | w ∈ F ∧ HasWinding ((edgeSubarc γ a b (le_of_lt (lt_trans _has _hsb))).trans q) w 1}
@[expose] def RightAtOn {x y : ℂ} (F : Set ℂ) (γ : Path x y) (s : {t : I // t ∈ openParams}) : Prop := ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b) (_hb : b < 1), ∃ q : Path (γ b) (γ a),
    Function.Injective q ∧ (∀ t : I, t ∈ openParams → q t ∈ F) ∧ γ s.1 ∈ closure {w : ℂ | w ∈ F ∧ HasWinding ((edgeSubarc γ a b (le_of_lt (lt_trans _has _hsb))).trans q) w (-1)}
end DirectedDistances.PlanarMap
namespace DirectedDistances.PlanarMap
open unitInterval
open scoped Topology
variable {V E : Type*}
namespace PlaneGraphDrawing
variable (D : PlaneGraphDrawing V E)
@[expose] def SideLeftOf (F : D.Face) (e : E) : Prop := ∀ s : {t : I // t ∈ openParams}, LeftAtOn F.val (D.arc e) s
@[expose] def SideRightOf (F : D.Face) (e : E) : Prop := ∀ s : {t : I // t ∈ openParams}, RightAtOn F.val (D.arc e) s
end PlaneGraphDrawing
end DirectedDistances.PlanarMap
namespace DirectedDistances.PlanarMap
open unitInterval
open scoped Topology
@[expose] def OrientationPreserving (f : ℂ ≃ₜ ℂ) : Prop := ∀ {z : ℂ} (L : Path z z) (w : ℂ), w ∉ Set.range L → ∀ n : ℤ, HasWinding L w n ↔ HasWinding (L.map f.continuous) (f w) n
end DirectedDistances.PlanarMap
namespace DirectedDistances.PaperProofs.Section3
open Set DirectedDistances.PlanarMap
open scoped ENNReal Topology
universe uV uE uV' uE'
@[expose] def d39GeomRootVertex {V E : Type*} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) : V := if rho.2 then M.toPlaneMapWithMissing.src rho.1 else M.toPlaneMapWithMissing.tgt rho.1
@[expose] def d39GeomAdj {V E : Type*} (M : DirectedPlaneMapWithMissing V E) (v w : V) : Prop := v ≠ w ∧ ∃ e : E, (M.toPlaneMapWithMissing.src e = v ∧ M.toPlaneMapWithMissing.tgt e = w) ∨ (M.toPlaneMapWithMissing.src e =
    w ∧ M.toPlaneMapWithMissing.tgt e = v)
@[expose] def d39GeomGraph {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) : SimpleGraph V where
  Adj := d39GeomAdj M
  symm := ⟨by
    intro v w h
    rcases h with ⟨hne, e, h | h⟩
    · exact ⟨hne.symm, e, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨hne.symm, e, Or.inl ⟨h.1, h.2⟩⟩⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩
@[expose] def d39GeomGraphDistance {V E : Type*} (M : DirectedPlaneMapWithMissing V E) (v w : V) : ℕ∞ := (d39GeomGraph M).edist v w
@[expose] def d39GeomBallVertices {V E : Type*} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) : Set V := {v | d39GeomGraphDistance M (d39GeomRootVertex M rho) v ≤ (r : ℕ∞)}
@[expose] def d39GeomBallEdges {V E : Type*} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) : Set E := {e | M.toPlaneMapWithMissing.src e ∈ d39GeomBallVertices M rho r ∧ M.toPlaneMapWithMissing.tgt e ∈
    d39GeomBallVertices M rho r}
@[expose] def d39GeomRetainedFaces {V E : Type*} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ) : Set (M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) := {F | ∀ v, M.toPlaneMapWithMissing.pos v ∈
    closure F.val → v ∈ d39GeomBallVertices M rho r}
theorem d39GeomRootEdge_mem {V : Type uV} {E : Type uE} {r : ℕ} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (hr : 0 < r) : rho.1 ∈ d39GeomBallEdges M rho r := by sorry
end DirectedDistances.PaperProofs.Section3
namespace DirectedDistances.PaperProofs.Section3
open Set DirectedDistances.PlanarMap unitInterval
open scoped ENNReal Topology
universe uV uE uV' uE'
structure D39GeomBallIsoV2 {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'} (r : ℕ) (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) where
  radius_pos : 0 < r
  h : ℂ ≃ₜ ℂ
  orientationPreserving : OrientationPreserving h
  vertexEquiv : {v // v ∈ d39GeomBallVertices M rho r} ≃ {v // v ∈ d39GeomBallVertices M' rho' r}
  edgeEquiv : {e // e ∈ d39GeomBallEdges M rho r} ≃ {e // e ∈ d39GeomBallEdges M' rho' r}
  faceEquiv : {F // F ∈ d39GeomRetainedFaces M rho r} ≃ {F // F ∈ d39GeomRetainedFaces M' rho' r}
  edgeFlip : {e // e ∈ d39GeomBallEdges M rho r} → Bool
  pos_map : ∀ v, h (M.toPlaneMapWithMissing.pos v.1) = M'.toPlaneMapWithMissing.pos (vertexEquiv v).1
  edgeParam : ∀ e, Homeomorph unitInterval unitInterval
  edgeParam_mono : ∀ e, edgeFlip e = false → StrictMono (edgeParam e)
  edgeParam_anti : ∀ e, edgeFlip e = true → StrictAnti (edgeParam e)
  arc_map : ∀ e t, h (M.toPlaneMapWithMissing.arc e.1 t) = M'.toPlaneMapWithMissing.arc (edgeEquiv e).1 (edgeParam e t)
  src_map : ∀ e, (vertexEquiv ⟨M.toPlaneMapWithMissing.src e.1, e.2.1⟩).1 = if edgeFlip e then M'.toPlaneMapWithMissing.tgt (edgeEquiv e).1 else M'.toPlaneMapWithMissing.src (edgeEquiv e).1
  tgt_map : ∀ e, (vertexEquiv ⟨M.toPlaneMapWithMissing.tgt e.1, e.2.2⟩).1 = if edgeFlip e then M'.toPlaneMapWithMissing.src (edgeEquiv e).1 else M'.toPlaneMapWithMissing.tgt (edgeEquiv e).1
  missing_map : ∀ e, M'.toPlaneMapWithMissing.missing (edgeEquiv e).1 ↔ M.toPlaneMapWithMissing.missing e.1
  orientation_map : ∀ e (he : ¬ M.toPlaneMapWithMissing.missing e.1),
    M'.forward ⟨(edgeEquiv e).1, by simpa [missing_map e] using he⟩ =
      Bool.xor (M.forward ⟨e.1, he⟩) (edgeFlip e)
  root_edge_map : (edgeEquiv ⟨rho.1, d39GeomRootEdge_mem M rho radius_pos⟩).1 = rho'.1
  root_bool_map : rho'.2 = Bool.xor rho.2 (edgeFlip ⟨rho.1, d39GeomRootEdge_mem M rho radius_pos⟩)
  face_image_map : ∀ F, h '' F.1 = (faceEquiv F).1
theorem d39GeomDistanceV2._proof_1 : Nat.AtLeastTwo ((1 : ℕ) + 1) := inferInstance
section
attribute [local instance 1000000] d39GeomDistanceV2._proof_1
@[expose] noncomputable def d39GeomDistanceV2 {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool)
    : ℝ≥0∞ :=
  ⨅ r : {r : ℕ // 0 < r},
    ⨅ (_ : Nonempty (D39GeomBallIsoV2 r.1 M rho M' rho')),
      ((1 / 2 : ℝ≥0∞) ^ r.1)
end
end DirectedDistances.PaperProofs.Section3
namespace DirectedDistances.PaperProofs.Section3
open Set DirectedDistances.PlanarMap
open scoped ENNReal
universe uV uE
structure D39GeomDomain {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) : Prop where
  connected : ∀ v w : V, (d39GeomGraph M).Reachable v w
  locallyFinite : ∀ v : V, ({e : E | M.toPlaneMapWithMissing.src e = v ∨ M.toPlaneMapWithMissing.tgt e = v}).Finite
  rootValid : M.toPlaneMapWithMissing.missing rho.1 ∨ ∃ h : ¬ M.toPlaneMapWithMissing.missing rho.1, M.forward ⟨rho.1, h⟩ = rho.2
end DirectedDistances.PaperProofs.Section3
namespace DirectedDistances.PaperProofs.Section3
open Set DirectedDistances.PlanarMap unitInterval
open scoped ENNReal Topology
universe uV uE uV' uE'
structure D39GeomRootedMapIsoV2 {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'} (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) where
  h : ℂ ≃ₜ ℂ
  orientationPreserving : OrientationPreserving h
  vertexEquiv : V ≃ V'
  edgeEquiv : E ≃ E'
  edgeFlip : E → Bool
  edgeParam : ∀ e, Homeomorph unitInterval unitInterval
  edgeParam_mono : ∀ e, edgeFlip e = false → StrictMono (edgeParam e)
  edgeParam_anti : ∀ e, edgeFlip e = true → StrictAnti (edgeParam e)
  pos_map : ∀ v, h (M.toPlaneMapWithMissing.pos v) = M'.toPlaneMapWithMissing.pos (vertexEquiv v)
  arc_map : ∀ e t, h (M.toPlaneMapWithMissing.arc e t) = M'.toPlaneMapWithMissing.arc (edgeEquiv e) (edgeParam e t)
  src_map : ∀ e, vertexEquiv (M.toPlaneMapWithMissing.src e) = if edgeFlip e then M'.toPlaneMapWithMissing.tgt (edgeEquiv e) else M'.toPlaneMapWithMissing.src (edgeEquiv e)
  tgt_map : ∀ e, vertexEquiv (M.toPlaneMapWithMissing.tgt e) = if edgeFlip e then M'.toPlaneMapWithMissing.src (edgeEquiv e) else M'.toPlaneMapWithMissing.tgt (edgeEquiv e)
  missing_map : ∀ e, M'.toPlaneMapWithMissing.missing (edgeEquiv e) ↔ M.toPlaneMapWithMissing.missing e
  orientation_map : ∀ e (he : ¬ M.toPlaneMapWithMissing.missing e),
    M'.forward ⟨edgeEquiv e, by simpa [missing_map e] using he⟩ =
      Bool.xor (M.forward ⟨e, he⟩) (edgeFlip e)
  root_edge_map : edgeEquiv rho.1 = rho'.1
  root_bool_map : rho'.2 = Bool.xor rho.2 (edgeFlip rho.1)
end DirectedDistances.PaperProofs.Section3
namespace DirectedDistances.PaperProofs.Section3
open DirectedDistances.PlanarMap Filter
open scoped ENNReal Topology
universe uV uE uV' uE'
structure D39DomainRootedMap.{u} where
  V : Type u
  E : Type u
  map : DirectedPlaneMapWithMissing V E
  root : E × Bool
  domain : D39GeomDomain map root
end DirectedDistances.PaperProofs.Section3
namespace DirectedDistances.PaperProofs.SourceResults
open Set DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open scoped ENNReal Topology
universe uD39V2 uV' uE'
structure D39DomainRootedMapV2 where
  V : Type uD39V2
  E : Type uD39V2
  map : DirectedPlaneMapWithMissing V E
  root : E × Bool
  domain : D39GeomDomain map root
end DirectedDistances.PaperProofs.SourceResults
namespace DirectedDistances.PlanarMap
open Equiv
abbrev RootedLocallyFiniteVertex (D : Type) (rot : Equiv.Perm D) := Quotient (Equiv.Perm.SameCycle.setoid rot)
@[expose] def rootedLocallyFiniteVertexClass {D : Type} (rot : Equiv.Perm D) (d : D) : RootedLocallyFiniteVertex D rot := Quotient.mk (Equiv.Perm.SameCycle.setoid rot) d
@[expose] def rootedLocallyFiniteDirectedStep {D : Type} (rot edgeInv : Equiv.Perm D) (missing tail : D → Prop) (v w : RootedLocallyFiniteVertex D rot) : Prop := ∃ d, ¬ missing d ∧ tail d ∧ rootedLocallyFiniteVertexClass
    rot d = v ∧ rootedLocallyFiniteVertexClass rot (edgeInv d) = w
open Equiv
structure D39MapCore where
  D : Type
  rot : Equiv.Perm D
  edgeInv : Equiv.Perm D
  edgeInv_invol : ∀ d, edgeInv (edgeInv d) = d
  edgeInv_ne : ∀ d, edgeInv d ≠ d
  missing : D → Prop
  missing_edgeInv : ∀ d, missing d ↔ missing (edgeInv d)
  tail : D → Prop
  tail_iff : ∀ d, ¬ missing d → (tail d ↔ ¬ tail (edgeInv d))
  tail_missing : ∀ d, missing d → ¬ tail d
  outer : D
  missing_outer : ∀ d, missing d → Equiv.Perm.SameCycle (rot.symm * edgeInv) outer d ∨ Equiv.Perm.SameCycle (rot.symm * edgeInv) outer (edgeInv d)
  locallyFinite : ∀ d, {e : D | rot.SameCycle d e}.Finite
  connected : ∀ d e, Relation.ReflTransGen (fun x y : D => y = rot x ∨ y = rot.symm x ∨ y = edgeInv x ∨ y = edgeInv.symm x) d e
  acyclic : ∀ v : RootedLocallyFiniteVertex D rot, ¬ Relation.TransGen (rootedLocallyFiniteDirectedStep rot edgeInv missing tail) v v
inductive D39RootMark (M : D39MapCore) where
  | present (d : M.D) (hp : ¬ M.missing d) (ht : M.tail d)
  | missing (d : M.D) (hm : M.missing d)
@[expose] def D39RootMark.dart {M : D39MapCore} (m : D39RootMark M) : M.D :=
  match m with
  | .present d _ _ => d
  | .missing d _ => d
structure D39RootedMap where
  core : D39MapCore
  rootMark : D39RootMark core
open Equiv
@[expose] def d39VertexClass (M : D39RootedMap) (d : M.core.D) : RootedLocallyFiniteVertex M.core.D M.core.rot := rootedLocallyFiniteVertexClass M.core.rot d
end DirectedDistances.PlanarMap
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
instance instMeasurableSpaceListFinOfNatNat_directedDistances : MeasurableSpace (List (Fin 3)) := ⊤
@[expose] noncomputable def excursionLength (ω : ℕ → Fin 3) : ℕ := (codeFstFirstHit (-1) ω).toNat
@[expose] noncomputable def excursionWord (ω : ℕ → Fin 3) : List (Fin 3) := (List.range (excursionLength ω)).map (fun i => ω (i + 1))
@[expose] noncomputable def excursionWordLaw : Measure (List (Fin 3)) := iidCodeMeasure.map excursionWord
instance : IsProbabilityMeasure excursionWordLaw := by
  unfold excursionWordLaw
  infer_instance
open MeasureTheory ProbabilityTheory
@[expose] noncomputable def uibhbotWordFamilyLaw : Measure (ℤ → List (Fin 3)) := Measure.infinitePi (fun _ : ℤ => excursionWordLaw)
instance : IsProbabilityMeasure uibhbotWordFamilyLaw := by
  unfold uibhbotWordFamilyLaw
  infer_instance
end DirectedDistances.RandomWalk
namespace DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults DirectedDistances.PaperProofs.Section3 unitInterval
open scoped Topology
structure D39DrawingRepresentationData (M : D39RootedMap) (B : D39DomainRootedMapV2) where
  vertexEquiv : RootedLocallyFiniteVertex M.core.D M.core.rot ≃ B.V
  positions_injective : Function.Injective B.map.toPlaneMapWithMissing.pos
  dartEquiv : M.core.D ≃ B.E × Bool
  dart_tail_vertex : ∀ d, vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot d) = if (dartEquiv d).2 then B.map.toPlaneMapWithMissing.src (dartEquiv d).1 else B.map.toPlaneMapWithMissing.tgt (dartEquiv d).1
  dart_head_vertex : ∀ d, vertexEquiv (rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d)) = if (dartEquiv d).2 then B.map.toPlaneMapWithMissing.tgt (dartEquiv d).1 else B.map.toPlaneMapWithMissing.src
    (dartEquiv d).1
  dart_edgeInv : ∀ d, dartEquiv (M.core.edgeInv d) = ((dartEquiv d).1, !(dartEquiv d).2)
  dart_missing : ∀ d, B.map.toPlaneMapWithMissing.missing (dartEquiv d).1 ↔ M.core.missing d
  dart_orientation : ∀ d (hd : ¬ M.core.missing d), M.core.tail d ↔ B.map.forward ⟨(dartEquiv d).1, (dart_missing d).not.mpr hd⟩ = (dartEquiv d).2
  root_mark : dartEquiv M.rootMark.dart = B.root
  faceOfDart : M.core.D → B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face
  faceOrbit_iff : ∀ d e, faceOfDart d = faceOfDart e ↔ Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e
  face_surjective : Function.Surjective faceOfDart
  face_left_of_dart : ∀ d, if (dartEquiv d).2 then B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideLeftOf (faceOfDart d) (dartEquiv d).1 else B.map.toPlaneMapWithMissing.toPlaneGraphDrawing.SideRightOf (faceOfDart d)
    (dartEquiv d).1
open DirectedDistances.PaperProofs.SourceResults DirectedDistances.PaperProofs.Section3 unitInterval
open scoped Topology
@[expose] def D39TopologicalCcwSuccessor {D : Type*} (star : Set D) (arc : D → I → ℂ) (d e : D) : Prop := ∃ H : ℂ ≃ₜ ℂ, OrientationPreserving H ∧ ∃ dir : D → ℂ, (∀ x ∈ star, dir x ≠ 0) ∧ (∀ x ∈ star, ∀ y ∈ star,
    Complex.arg (dir x) = Complex.arg (dir y) → x = y) ∧ CcwSuccessor star dir d e ∧ ∀ x ∈ star, ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ H '' (arc x '' Set.Icc (0 : I) t) = {z : ℂ | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (s : ℂ) *
    dir x}
@[expose] def d39DrawingDartArc (B : D39DomainRootedMapV2) (data : D39DrawingRepresentationData M B) (d : M.core.D) : I → ℂ := if (data.dartEquiv d).2 then B.map.toPlaneMapWithMissing.arc (data.dartEquiv d).1 else
    (B.map.toPlaneMapWithMissing.arc (data.dartEquiv d).1).symm
structure D39DrawingRepresentationData3 (M : D39RootedMap) (B : D39DomainRootedMapV2) extends D39DrawingRepresentationData M B where
  rotation_topological_successor : ∀ d, D39TopologicalCcwSuccessor {e | rootedLocallyFiniteVertexClass M.core.rot e = rootedLocallyFiniteVertexClass M.core.rot d} (d39DrawingDartArc B toD39DrawingRepresentationData) d
    (M.core.rot d)
  vertex_frontier_incidence : ∀ d v, B.map.toPlaneMapWithMissing.pos (toD39DrawingRepresentationData.vertexEquiv v) ∈ frontier (toD39DrawingRepresentationData.faceOfDart d).val ↔ ∃ e, Equiv.Perm.SameCycle
    (M.core.rot.symm * M.core.edgeInv) d e ∧ rootedLocallyFiniteVertexClass M.core.rot e = v
end DirectedDistances.PlanarMap
namespace DirectedDistances.PaperProofs.Section5
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk MeasureTheory
theorem uibhbotDefaultBlockLetterRel._proof_1 : @NeZero ℕ (@Zero.ofOfNat0 ℕ _) ((2 : ℕ) + 1) := ⟨by decide⟩
section
attribute [local instance 1000000] uibhbotDefaultBlockLetterRel._proof_1
@[expose] def uibhbotDefaultBlockLetterRel (f : ℕ → List (Fin 3)) (n : ℕ) : Fin 3 := (((List.range (n + 1)).flatMap f)[n]?).getD 0
end
@[expose] def uibhbotCodeWordRel (w : ℤ → List (Fin 3)) (t : ℤ) : Fin 3 := if 0 ≤ t then uibhbotDefaultBlockLetterRel (fun k => w (k : ℤ)) t.toNat else uibhbotDefaultBlockLetterRel (fun k => (w (-(k : ℤ) - 1)).reverse)
    (-t - 1).toNat
@[expose] noncomputable def uibhbotCodeLawRel : ProbabilityMeasure (ℤ → Fin 3) := by
  exact ⟨uibhbotWordFamilyLaw.map uibhbotCodeWordRel, inferInstance⟩
end DirectedDistances.PaperProofs.Section5
namespace DirectedDistances.PlanarMap
namespace Polyline
@[expose] def listPath (a : ℂ) : (l : List ℂ) → Path a ((a :: l).getLast (by simp))
  | [] => Path.refl a
  | [b] => Path.segment a b
  | b :: c :: l => (Path.segment a b).trans (listPath b (c :: l))
theorem toPath._proof_3 (p : Polyline) (a : ℂ) (l : List ℂ) (h : p.points = a :: l) : p.start = a := by simp [start, h]
theorem toPath._proof_4 (p : Polyline) (a : ℂ) (l : List ℂ) (h : p.points = a :: l) : p.finish = (a :: l).getLast (listPath._proof_1 a l) := by simp [finish, h]
@[expose] def toPath (p : Polyline) : Path p.start p.finish :=
  match h : p.points with
  | [] => False.elim (p.nonempty h)
  | a :: l => (listPath a l).cast (toPath._proof_3 p a l h) (toPath._proof_4 p a l h)
theorem toPath_injOn (p : Polyline) (hlen : 2 ≤ p.points.length) (h : p.IsSimple) : Set.InjOn p.toPath openParams := by sorry
theorem toPath_image_openParams (p : Polyline) (hlen : 2 ≤ p.points.length) (h : p.IsSimple) : p.toPath '' openParams = p.interior := by sorry
end Polyline
namespace PLDrawing
variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
@[expose] def edgeSetoid (P : PLDrawing D V flip rot vert) : Setoid D where
  r d e := d = e ∨ d = flip e
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · rintro d e (h | h)
      · exact Or.inl h.symm
      · exact Or.inr ((P.flip_involutive e).symm.trans (congrArg flip h.symm))
    · rintro d e f (rfl | hde) hef
      · exact hef
      · rcases hef with rfl | hef
        · exact Or.inr hde
        · exact Or.inl (hde.trans ((congrArg flip hef).trans (P.flip_involutive f)))
abbrev GeometricEdge (P : PLDrawing D V flip rot vert) := Quotient P.edgeSetoid
variable (P : PLDrawing D V flip rot vert)
theorem geometricEdge_flip (d : D) : Quotient.mk P.edgeSetoid (flip d) = Quotient.mk P.edgeSetoid d := by sorry
@[expose] def toPlaneGraphDrawing : PlaneGraphDrawing V P.GeometricEdge where
  src e := vert e.out
  tgt e := vert (flip e.out)
  pos := P.pos
  pos_injective := P.pos_injective
  arc e := (P.arc e.out).toPath.cast (P.arc_start e.out).symm (P.arc_finish e.out).symm
  arc_injOn e := (P.arc e.out).toPath_injOn (P.arc_length e.out) (P.arc_simple e.out)
  openArc_disjoint := by
    intro e f hef
    change Disjoint ((P.arc e.out).toPath '' openParams)
      ((P.arc f.out).toPath '' openParams)
    rw [Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _),
      Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)]
    apply P.interior_disjoint
    · intro h
      apply hef
      exact (Quotient.out_eq e).symm.trans
        ((congrArg (Quotient.mk P.edgeSetoid) h.symm).trans (Quotient.out_eq f))
    · intro h
      apply hef
      exact (Quotient.out_eq e).symm.trans
        (((P.geometricEdge_flip e.out).symm.trans
          (congrArg (Quotient.mk P.edgeSetoid) h.symm)).trans (Quotient.out_eq f))
  openArc_avoids := by
    intro e v
    change P.pos v ∉ (P.arc e.out).toPath '' openParams
    rw [Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)]
    exact P.interior_avoids_vertices e.out v
end PLDrawing
end DirectedDistances.PlanarMap
namespace DirectedDistances.PaperProofs.Section5
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.SourceResults DirectedDistances.PaperProofs.Section3
theorem plDrawing_geometricEdge_finite {D V : Type*} [Finite D] {flip : D → D} {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert) : Finite P.GeometricEdge := by
  classical
  exact Finite.of_surjective (Quotient.mk P.edgeSetoid) Quotient.mk_surjective
theorem d39GeomDomain_of_finite_edgeCarrier {V E : Type*} [Finite E] (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (hconn : ∀ v w : V, (d39GeomGraph M).Reachable v w) (hroot : M.toPlaneMapWithMissing.missing
    rho.1 ∨ ∃ h : ¬ M.toPlaneMapWithMissing.missing rho.1, M.forward ⟨rho.1, h⟩ = rho.2) : D39GeomDomain M rho := by sorry
@[expose] def finitePLDrawingDirectedMap {D V : Type u} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert) (missing : P.GeometricEdge → Prop) (forward : {e : P.GeometricEdge // ¬ missing
    e} → Bool) (hmissingExternal : ∀ e, missing e → ∃ F : P.toPlaneGraphDrawing.Face, PlaneGraphDrawing.IsExternal P.toPlaneGraphDrawing F ∧ Set.range (P.toPlaneGraphDrawing.arc e) ⊆ closure F.val) :
    DirectedPlaneMapWithMissing V P.GeometricEdge :=
  { toPlaneMapWithMissing :=
      { toPlaneGraphDrawing := P.toPlaneGraphDrawing
        missing := missing
        missing_on_external := hmissingExternal }
    forward := forward }
@[expose] noncomputable def d39FiniteDomainRootedMapV2 {V E : Type u} [Finite E] (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (hconn : ∀ v w : V, (d39GeomGraph M).Reachable v w) (hroot :
    M.toPlaneMapWithMissing.missing rho.1 ∨ ∃ h : ¬ M.toPlaneMapWithMissing.missing rho.1, M.forward ⟨rho.1, h⟩ = rho.2) : D39DomainRootedMapV2 := ⟨V, E, M, rho, d39GeomDomain_of_finite_edgeCarrier M rho hconn hroot⟩
end DirectedDistances.PaperProofs.Section5
section BusemannInterface
set_option bootstrap.genMatcherCode false
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
section StageRotationView
@[expose] def stageRot (w : ℕ → Fin 3) :
    (n : ℕ) → Equiv.Perm (StageDart (kmswStage w n).nextEdge)
  | 0 => 1
  | n + 1 => StageRotation.step (kmswStage w n)
      (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n) (w n)
variable (w : ℕ → Fin 3) (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
include hfin in
theorem kmswInfRot_existsUnique : ∃! σ : Equiv.Perm (ℕ × Bool), (∀ n (x : StageDart (kmswStage w n).nextEdge), kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) → σ (x.1.val, x.2) = ((stageRot w n x).1.val,
    (stageRot w n x).2)) ∧ (∀ n (x : StageDart (kmswStage w n).nextEdge), kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) → σ.symm (x.1.val, x.2) = (((stageRot w n).symm x).1.val, ((stageRot w n).symm x).2)) := by sorry
@[expose] noncomputable def kmswInfRot : Equiv.Perm (ℕ × Bool) := (kmswInfRot_existsUnique w hfin).exists.choose
end StageRotationView
@[expose] def KMSWWindowPatchData.step (G F : State) (c : Step)
    (d : KMSWWindowPatchData) : KMSWWindowPatchData :=
  let alloc := fun e => if e < F.nextEdge then d.φ e else G.nextEdge + (e - F.nextEdge)
  match c with
  | .down => match F.UR with
    | _ :: _ => d
    | [] => match d.B with
      | [] => { d with φ := alloc, XR := d.XR ++ [F.nextEdge] }
      | q :: bs =>
        { d with
          φ := fun e => if e < F.nextEdge then d.φ e else q
          B := bs
          YR := d.YR ++ [F.nextEdge] }
  | .up => { d with φ := alloc }
  | .left => match F.UL.dropLast.reverse with
    | _ :: _ => { d with φ := alloc }
    | [] => match d.A.reverse with
      | [] => { d with φ := alloc, XL := (F.nextEdge + 1) :: d.XL }
      | q :: es =>
        { d with
          φ := fun e => if e < F.nextEdge then d.φ e else
            if e = F.nextEdge then G.nextEdge else q
          A := es.reverse
          YL := (F.nextEdge + 1) :: d.YL }
@[expose] def kmswWindowPatchData (w : ℕ → Fin 3) (s : ℕ) : ℕ → KMSWWindowPatchData
  | 0 => ⟨fun _ => (kmswStage w s).active,
      (kmswStage w s).UL.dropLast, (kmswStage w s).UR, [], [], [], []⟩
  | j + 1 => KMSWWindowPatchData.step (kmswStage w (s + j))
      (kmswStage (fun i => w (s + i)) j) (kmswCodeStep (w (s + j)))
      (kmswWindowPatchData w s j)
end DLQG1.Palomar.Model.KMSW
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def kmswWindowPatchVertexMap (w : ℕ → Fin 3) (s : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun v => if v = 0 then (kmswStage w s).west (kmswStage w s).active
      else (kmswStage w s).east (kmswStage w s).active
  | j + 1 =>
      let G := kmswStage w (s + j)
      let F := kmswStage (fun i => w (s + i)) j
      let d := kmswWindowPatchData w s j
      let ψ := kmswWindowPatchVertexMap w s j
      let extend := fun z v => if v < F.nextVertex then ψ v else z
      match kmswCodeStep (w (s + j)) with
      | .down => match F.UR with
        | _ :: _ => ψ
        | [] => match d.B with
          | [] => extend G.nextVertex
          | q :: _ => extend (G.east q)
      | .up => extend G.nextVertex
      | .left => match F.UL.dropLast.reverse with
        | _ :: _ => ψ
        | [] => match d.A.reverse with
          | [] => extend G.nextVertex
          | q :: _ => extend (G.west q)
open DirectedDistances.KMSW
@[expose] def kmswWindowEdgeMapInf (w : ℕ → Fin 3) (s e : ℕ) : ℕ := (kmswWindowPatchData w s e).φ e
@[expose] def kmswWindowVertexMapInf (w : ℕ → Fin 3) (s v : ℕ) : ℕ := kmswWindowPatchVertexMap w s (4 * v + 1) v
open DirectedDistances.KMSW
@[expose] def shiftedStream (W : ℤ → Fin 3) (N : ℕ) : ℕ → Fin 3 := fun i => W ((i : ℤ) - N)
@[expose] def wholePlaneEdgeTrans (W : ℤ → Fin 3) (N N' : ℕ) (_h : N ≤ N') : ℕ → ℕ := kmswWindowEdgeMapInf (shiftedStream W N') (N' - N)
@[expose] def wholePlaneVertexTrans (W : ℤ → Fin 3) (N N' : ℕ) (_h : N ≤ N') : ℕ → ℕ := kmswWindowVertexMapInf (shiftedStream W N') (N' - N)
@[expose] def wholePlaneEdgeRel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) : Prop := ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M, wholePlaneEdgeTrans W a.1 M ha a.2 = wholePlaneEdgeTrans W b.1 M hb b.2
@[expose] def wholePlaneVertexRel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) : Prop := ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M, wholePlaneVertexTrans W a.1 M ha a.2 = wholePlaneVertexTrans W b.1 M hb b.2
theorem wholePlaneEdgeRel_equivalence (W : ℤ → Fin 3) : Equivalence (wholePlaneEdgeRel W) := by sorry
theorem wholePlaneVertexRel_equivalence (W : ℤ → Fin 3) : Equivalence (wholePlaneVertexRel W) := by sorry
@[expose] def wholePlaneEdgeSetoid (W : ℤ → Fin 3) : Setoid (Σ _ : ℕ, ℕ) where
  r := wholePlaneEdgeRel W
  iseqv := wholePlaneEdgeRel_equivalence W
@[expose] def wholePlaneVertexSetoid (W : ℤ → Fin 3) : Setoid (Σ _ : ℕ, ℕ) where
  r := wholePlaneVertexRel W
  iseqv := wholePlaneVertexRel_equivalence W
@[expose] def WholePlaneEdge (W : ℤ → Fin 3) : Type := Quotient (wholePlaneEdgeSetoid W)
@[expose] def WholePlaneVertex (W : ℤ → Fin 3) : Type := Quotient (wholePlaneVertexSetoid W)
@[expose] def wholePlaneEdgeι (W : ℤ → Fin 3) (N : ℕ) (e : ℕ) : WholePlaneEdge W := Quotient.mk (wholePlaneEdgeSetoid W) ⟨N, e⟩
@[expose] def wholePlaneVertexι (W : ℤ → Fin 3) (N : ℕ) (v : ℕ) : WholePlaneVertex W := Quotient.mk (wholePlaneVertexSetoid W) ⟨N, v⟩
theorem wholePlaneEdgeRel_west (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneEdgeRel W a b) : wholePlaneVertexι W a.1 (edgeWest (shiftedStream W a.1) a.2) = wholePlaneVertexι W b.1 (edgeWest (shiftedStream W b.1)
    b.2) := by sorry
theorem wholePlaneEdgeRel_east (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneEdgeRel W a b) : wholePlaneVertexι W a.1 (edgeEast (shiftedStream W a.1) a.2) = wholePlaneVertexι W b.1 (edgeEast (shiftedStream W b.1)
    b.2) := by sorry
open DirectedDistances.KMSW
@[expose] def KMSWFiniteIncidence (w : ℕ → Fin 3) : Prop := ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧ ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite
@[expose] def wholePlaneFresh (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') (v : ℕ) : Prop := (kmswStage (shiftedStream W N') (N' - N)).nextVertex ≤ wholePlaneVertexTrans W N N' h v
@[expose] def WholePlaneRotationHypothesis (W : ℤ → Fin 3) : Prop := (∀ N, KMSWFiniteIncidence (shiftedStream W N)) ∧ (∀ N v, ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'), wholePlaneFresh W M M' hMM' (wholePlaneVertexTrans W
    N M hNM v))
@[expose] def wholePlaneDartTrans (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') (d : ℕ × Bool) : ℕ × Bool := (wholePlaneEdgeTrans W N N' h d.1, d.2)
@[expose] def wholePlaneDartι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) : WholePlaneEdge W × Bool := (wholePlaneEdgeι W N d.1, d.2)
open DirectedDistances.KMSW
@[expose] def WholePlaneDart (W : ℤ → Fin 3) : Type := WholePlaneEdge W × Bool
@[expose] noncomputable def runRot (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) : Equiv.Perm (ℕ × Bool) := if inv then (kmswInfRot (shiftedStream W N) (H.1 N)).symm else kmswInfRot
    (shiftedStream W N) (H.1 N)
@[expose] def eventualValue (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) (y : WholePlaneDart W) : Prop := ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'), wholePlaneDartι W M' (runRot
    W H inv M' (wholePlaneDartTrans W N M' (hNM.trans hMM') d)) = y
theorem eventualValue_existsUnique (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) : ∃! y, eventualValue W H inv N d y := by sorry
@[expose] noncomputable def value (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) : WholePlaneDart W := (eventualValue_existsUnique W H inv N d).exists.choose
theorem value_rel (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (inv : Bool) (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneEdgeRel W a b) (s : Bool) : value W H inv a.1 (a.2, s) = value W H inv b.1 (b.2, s) := by sorry
@[expose] noncomputable def wholePlaneRot (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) : WholePlaneDart W → WholePlaneDart W :=
  fun x => Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    Classical.choose (show ∃ y : WholePlaneDart W,
      ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
        wholePlaneDartι W L (kmswInfRot (shiftedStream W L) (H.1 L)
          (wholePlaneDartTrans W a.1 L (hNM.trans hML) (a.2, x.2))) = y from by
            exact (eventualValue_existsUnique W H false a.1 (a.2, x.2)).exists))
    (by
      intro a b hab
      exact value_rel W H false a b hab x.2) x.1
@[expose] noncomputable def wholePlaneRotInv (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) : WholePlaneDart W → WholePlaneDart W :=
  fun x => Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    Classical.choose (show ∃ y : WholePlaneDart W,
      ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
        wholePlaneDartι W L ((kmswInfRot (shiftedStream W L) (H.1 L)).symm
          (wholePlaneDartTrans W a.1 L (hNM.trans hML) (a.2, x.2))) = y from by
            exact (eventualValue_existsUnique W H true a.1 (a.2, x.2)).exists))
    (by
      intro a b hab
      exact value_rel W H true a b hab x.2) x.1
theorem wholePlaneRot_comp_inv (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) : wholePlaneRot W H ∘ wholePlaneRotInv W H = id := by sorry
theorem wholePlaneRotInv_comp_rot (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) : wholePlaneRotInv W H ∘ wholePlaneRot W H = id := by sorry
@[expose] noncomputable def wholePlaneRotation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Equiv.Perm (WholePlaneDart W) where
  toFun := wholePlaneRot W H
  invFun := wholePlaneRotInv W H
  left_inv := congrFun (wholePlaneRotInv_comp_rot W H)
  right_inv := congrFun (wholePlaneRot_comp_inv W H)
open DirectedDistances.KMSW
@[expose] def wholePlaneDartFlip (W : ℤ → Fin 3) : Equiv.Perm (WholePlaneDart W) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl
@[expose] def eventualPresence (W : ℤ → Fin 3) (N e : ℕ) : Prop := ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L), EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W N L (hNM.trans hML) e)
theorem eventualPresence_rel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneEdgeRel W a b) : eventualPresence W a.1 a.2 = eventualPresence W b.1 b.2 := by sorry
@[expose] def wholePlaneEdgePresent (W : ℤ → Fin 3) : WholePlaneEdge W → Prop :=
  Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
      EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W a.1 L (hNM.trans hML) a.2))
    (by
      intro a b hab
      exact eventualPresence_rel W a b hab)
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk Quiver
@[expose] def wholePlaneDartTail (W : ℤ → Fin 3) : WholePlaneDart W → Prop := fun d => ¬ d.2 ∧ wholePlaneEdgePresent W d.1
end DLQG1.Palomar.Model.KMSW
end BusemannInterface
namespace DLQG1.Palomar.GeometryInterface
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5
open scoped ENNReal Topology
abbrev related (A B : D39DomainRootedMap.{0}) : Prop := Nonempty (D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
theorem related_equivalence : Equivalence related := by sorry
abbrev domainSetoid : Setoid D39DomainRootedMap.{0} where
  r := related
  iseqv := related_equivalence
abbrev MapClass := Quotient domainSetoid
theorem distance_respects : ∀ A B A' B' : D39DomainRootedMap.{0}, related A A' → related B B' → d39GeomDistanceV2 A.map A.root B.map B.root = d39GeomDistanceV2 A'.map A'.root B'.map B'.root := by sorry
abbrev distance (c d : MapClass) : ℝ≥0∞ := Quotient.liftOn₂ c d (fun A B => d39GeomDistanceV2 A.map A.root B.map B.root) distance_respects
theorem distance_self (c : MapClass) : distance c c = 0 := by sorry
theorem distance_comm (c d : MapClass) : distance c d = distance d c := by sorry
theorem distance_triangle (c d e : MapClass) : distance c e ≤ distance c d + distance d e := by sorry
abbrev metric : PseudoEMetricSpace MapClass where
  edist := distance
  edist_self := distance_self
  edist_comm := distance_comm
  edist_triangle := distance_triangle
abbrev topology : TopologicalSpace MapClass := metric.toUniformSpace.toTopologicalSpace
def classOf (B : DirectedDistances.PaperProofs.SourceResults.D39DomainRootedMapV2.{0}) : MapClass := Quotient.mk domainSetoid ⟨B.V, B.E, B.map, B.root, B.domain⟩
end DLQG1.Palomar.GeometryInterface
attribute [local instance] DLQG1.Palomar.GeometryInterface.metric DLQG1.Palomar.GeometryInterface.topology
@[expose] public section
namespace DLQG1.Palomar.HalfPlaneCode
open DirectedDistances.PlanarMap DirectedDistances.KMSW DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5 DirectedDistances.PaperProofs.SourceResults
def rootDart (W : ℤ → Fin 3) : DLQG1.Palomar.Model.KMSW.WholePlaneDart W := DLQG1.Palomar.Model.KMSW.wholePlaneDartι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1, false)
def outerDart (W : ℤ → Fin 3) : DLQG1.Palomar.Model.KMSW.WholePlaneDart W := DLQG1.Palomar.Model.KMSW.wholePlaneDartFlip W (rootDart W)
def IsCodeMap (W : ℤ → Fin 3) (H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W) (M : D39RootedMap) : Prop := ∃ e : M.core.D ≃ DLQG1.Palomar.Model.KMSW.WholePlaneDart W, (∀ d, e (M.core.rot d) =
    DLQG1.Palomar.Model.KMSW.wholePlaneRotation W H (e d)) ∧ (∀ d, e (M.core.edgeInv d) = DLQG1.Palomar.Model.KMSW.wholePlaneDartFlip W (e d)) ∧ (∀ d, M.core.missing d ↔ ¬ DLQG1.Palomar.Model.KMSW.wholePlaneEdgePresent W
    (e d).1) ∧ (∀ d, M.core.tail d ↔ DLQG1.Palomar.Model.KMSW.wholePlaneDartTail W (e d)) ∧ e M.core.outer = outerDart W ∧ e M.rootMark.dart = rootDart W ∧ M.core.missing M.rootMark.dart
end DLQG1.Palomar.HalfPlaneCode
namespace DLQG1.Palomar.GeometryLawMinimal
open DirectedDistances.PlanarMap DirectedDistances.KMSW DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5 DirectedDistances.PaperProofs.SourceResults MeasureTheory Set Filter DLQG1.Palomar.HalfPlaneCode
open scoped ENNReal Topology
local instance lawMeasurable : MeasurableSpace DLQG1.Palomar.GeometryInterface.MapClass :=
  borel DLQG1.Palomar.GeometryInterface.MapClass
local instance lawBorel : BorelSpace DLQG1.Palomar.GeometryInterface.MapClass := ⟨rfl⟩
def RealizesCode (W : ℤ → Fin 3) (c : DLQG1.Palomar.GeometryInterface.MapClass) : Prop := ∃ (H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W) (M : D39RootedMap), IsCodeMap W H M ∧ ∃ (B :
    D39DomainRootedMapV2.{0}) (x : D39DrawingRepresentationData3 M B) (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot) M.core.edgeInv M.core.rot (d39VertexClass M)),
    B.map.toPlaneMapWithMissing.missing B.root.1 ∧ (∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v)) ∧ (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧ ∀ t, d39DrawingDartArc B
    x.toD39DrawingRepresentationData d t = (P.arc d).toPath (φ t)) ∧ {d | Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) (M.core.edgeInv M.rootMark.dart) d}.Infinite ∧ c = DLQG1.Palomar.GeometryInterface.classOf
    B
def IsSourceLaw (μ : ProbabilityMeasure DLQG1.Palomar.GeometryInterface.MapClass) : Prop := ∃ f : (ℤ → Fin 3) → DLQG1.Palomar.GeometryInterface.MapClass, Measurable f ∧ (∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    RealizesCode W (f W)) ∧ μ = uibhbotCodeLawRel.map f
theorem existsUnique_sourceLaw : ∃! μ : ProbabilityMeasure DLQG1.Palomar.GeometryInterface.MapClass, IsSourceLaw μ := by sorry
def sourceLaw : ProbabilityMeasure DLQG1.Palomar.GeometryInterface.MapClass := Classical.choose existsUnique_sourceLaw.exists
end DLQG1.Palomar.GeometryLawMinimal
namespace DLQG1.Palomar.DiskSampler
open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5
@[expose] abbrev Codes (ell n : ℕ) := KMSWLeftWalkClass (ell + 1) n
@[expose] abbrev CodeSample (ell n : ℕ) := Codes ell n × Fin ell
@[expose] instance codeMeasurableSpace (ell n : ℕ) : MeasurableSpace (Codes ell n) := ⊤
@[expose] def codeMeasure (ell n : ℕ) : Measure (CodeSample ell n) := (uniformCountingMeasure (Codes ell n)).prod (uniformCountingMeasure (Fin ell))
theorem codeMeasure_probability (ell n : ℕ) (hell : 0 < ell) (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) : IsProbabilityMeasure (codeMeasure ell n) := by sorry
@[expose] def codeStream {ell n : ℕ} (c : Codes ell n) : ℕ → Fin 3 := DirectedDistances.KMSW.finiteCodeExtend (n := n + 1) c.val
end DLQG1.Palomar.DiskSampler
@[expose] public section
namespace DLQG1.Palomar.DiskMinimal
open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section5 DirectedDistances.PaperProofs.SourceResults DLQG1.Palomar.DiskSampler DLQG1.Palomar.GeometryInterface
attribute [local instance] DLQG1.Palomar.GeometryInterface.metric
attribute [local instance] DLQG1.Palomar.GeometryInterface.topology
@[expose] local instance modelMeasurable : MeasurableSpace MapClass := borel MapClass
local instance modelBorel : BorelSpace MapClass := ⟨rfl⟩
theorem firstHit_exists {ell n : ℕ} (c : Codes ell n) (j : Fin ell) : ∃ m, L (codeStream c) m = -((j.val + 1 : ℕ) : ℤ) := by sorry
@[expose] def firstHit {ell n : ℕ} (c : Codes ell n) (j : Fin ell) : ℕ := Nat.find (firstHit_exists c j)
theorem rootEdge_bound {ell n : ℕ} (c : Codes ell n) (j : Fin ell) : kmswLLCreatedEdge (codeStream c) (firstHit c j) < (kmswStage (codeStream c) n).nextEdge := by sorry
@[expose] def rootDart {ell n : ℕ} (c : Codes ell n) (j : Fin ell) : StageDart (kmswStage (codeStream c) n).nextEdge := (⟨kmswLLCreatedEdge (codeStream c) (firstHit c j), rootEdge_bound c j⟩, false)
theorem outer_nonempty (w : ℕ → Fin 3) (n : ℕ) : (kmswStage w n).UL ≠ [] := by sorry
theorem outer_head_bound (w : ℕ → Fin 3) (n : ℕ) : (kmswStage w n).UL.head (outer_nonempty w n) < (kmswStage w n).nextEdge := by sorry
@[expose] def outerDart (w : ℕ → Fin 3) (n : ℕ) : StageDart (kmswStage w n).nextEdge := (⟨(kmswStage w n).UL.head (outer_nonempty w n), outer_head_bound w n⟩, false)
@[expose] def outer (w : ℕ → Fin 3) (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) : Prop := Equiv.Perm.SameCycle ((stageRot w n)⁻¹ * edgeFlip _) (outerDart w n) d
structure DrawingData {ell n : ℕ} (c : Codes ell n) where
  drawing : StageDrawing (codeStream c) n
  face : drawing.Face
  unbounded : drawing.IsUnbounded face
  border : ∀ d, drawing.dartBorders d face ↔ outer (codeStream c) n d
theorem drawingData_nonempty (ell n : ℕ) (hell : 0 < ell) (c : Codes ell n) : Nonempty (DrawingData c) := by sorry
@[expose] def drawingData (ell n : ℕ) (hell : 0 < ell) (c : Codes ell n) : DrawingData c := Classical.choice (drawingData_nonempty ell n hell c)
@[expose] def missing {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) : D.drawing.GeometricEdge → Prop := fun e => (kmswStage (codeStream c) n).present e.out.1.val = false
@[expose] def forward {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) : {e : D.drawing.GeometricEdge // ¬ missing D e} → Bool := fun e => !e.val.out.2
theorem missing_external {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) : ∀ e, missing D e → ∃ F : D.drawing.toPlaneGraphDrawing.Face, PlaneGraphDrawing.IsExternal D.drawing.toPlaneGraphDrawing F ∧ Set.range
    (D.drawing.toPlaneGraphDrawing.arc e) ⊆ closure F.val := by sorry
@[expose] def map {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) := finitePLDrawingDirectedMap D.drawing (missing D) (forward D) (missing_external D)
theorem connected {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) : ∀ v v' : Fin (kmswStage (codeStream c) n).nextVertex, (d39GeomGraph (map D)).Reachable v v' := by sorry
@[expose] def root {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) (j : Fin ell) : D.drawing.GeometricEdge × Bool := (Quotient.mk D.drawing.edgeSetoid (rootDart c j), decide (rootDart c j = (Quotient.mk
    D.drawing.edgeSetoid (rootDart c j)).out))
theorem root_missing {ell n : ℕ} {c : Codes ell n} (D : DrawingData c) (j : Fin ell) : (map D).toPlaneMapWithMissing.missing (root D j).1 := by sorry
@[expose] def domain {ell n : ℕ} (c : Codes ell n) (j : Fin ell) (D : DrawingData c) : D39DomainRootedMapV2 := by
  letI : Finite D.drawing.GeometricEdge := plDrawing_geometricEdge_finite D.drawing
  exact d39FiniteDomainRootedMapV2 (map D) (root D j)
    (connected D) (Or.inl (root_missing D j))
@[expose] def finiteClass (ell n : ℕ) (hell : 0 < ell) (p : CodeSample ell n) : MapClass := DLQG1.Palomar.GeometryInterface.classOf (domain p.1 p.2 (drawingData ell n hell p.1))
theorem measurable_finiteClass (ell n : ℕ) (hell : 0 < ell) : Measurable (finiteClass ell n hell) := by sorry
theorem finiteClass_probability (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) : IsProbabilityMeasure ((codeMeasure ell n).map (finiteClass ell n hell)) := by sorry
@[expose] def finiteLaw (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) : ProbabilityMeasure MapClass := ⟨(codeMeasure ell n).map (finiteClass ell n hell),
    finiteClass_probability n ell hell hle hmod⟩
end DLQG1.Palomar.DiskMinimal
namespace DLQG1.Palomar.Principal
open MeasureTheory Filter DLQG1.Palomar.DiskMinimal
attribute [local instance] DLQG1.Palomar.GeometryInterface.metric
attribute [local instance] DLQG1.Palomar.GeometryInterface.topology
attribute [local instance] DLQG1.Palomar.DiskMinimal.modelMeasurable
attribute [local instance] DLQG1.Palomar.DiskMinimal.modelBorel
theorem disk_local_limit (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ) (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧ ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q) (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ)) (hhi : ∀
    k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) : Tendsto (fun k => finiteLaw (k + 1) (ell k) (hadm k).1 (hadm k).2.1 (hadm k).2.2) atTop (nhds DLQG1.Palomar.GeometryLawMinimal.sourceLaw) := by sorry
end DLQG1.Palomar.Principal
