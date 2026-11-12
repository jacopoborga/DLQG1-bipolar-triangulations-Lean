module
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.List.GetD
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Moments.SubGaussian
/-! Source-matched standalone ordinary-definition slice for Theorem 1.7 (Busemann increment laws).
This Challenge has thirteen constructor theorem holes and its one main theorem hole.
It has no definition holes; the comparator checks it against its separate Solution. -/
public section
-- Source module DirectedDistances.KMSW.Walk
namespace DirectedDistances.KMSW
inductive Step
  | down
  | left
  | up
  deriving DecidableEq
end DirectedDistances.KMSW
-- Source module DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
@[expose] def lazyTwoDimensionalStep (c : Fin 3) : ℤ × ℤ :=
  ((c : ℤ) - 1, if c = 0 then 0 else if c = 1 then 1 else -1)
end DirectedDistances.RandomWalk
-- Source module DirectedDistances.KMSW.BoundaryDynamics
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
/-- Public natural-number typing witness; explicit to preserve source elaboration. -/
theorem kmswCodeStep._proof_1 :
    @NeZero ℕ (@Zero.ofOfNat0 ℕ _) ((2 : ℕ) + 1) := ⟨by decide⟩
section
attribute [local instance 1000000] kmswCodeStep._proof_1
@[expose] def kmswCodeStep (c : Fin 3) : Step :=
  if c = 0 then .left else if c = 1 then .up else .down
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
@[expose] def kmswStep (s : State) (c : Fin 3) : State :=
  kmswStepOfStep s (kmswCodeStep c)
@[expose] def kmswStage (w : ℕ → Fin 3) : ℕ → State
  | 0 => kmswInit
  | n + 1 => kmswStep (kmswStage w n) (w n)
@[expose] def L (w : ℕ → Fin 3) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (RandomWalk.lazyTwoDimensionalStep (w i)).1
@[expose] def R (w : ℕ → Fin 3) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (RandomWalk.lazyTwoDimensionalStep (w i)).2
end DirectedDistances.KMSW
-- Source module DirectedDistances.KMSW.BoundaryRecordsUL
namespace DirectedDistances.KMSW
open scoped Classical
@[expose] def act (w : ℕ → Fin 3) (m : ℕ) : ℕ := (kmswStage w m).active
theorem act_lt_nextEdge (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    act w m < (kmswStage w n).nextEdge := by sorry
end DirectedDistances.KMSW
-- Source module DirectedDistances.KMSW.CutEquivalence
namespace DirectedDistances.KMSW
open scoped Classical
@[expose] def edgeWest (w : ℕ → Fin 3) (e : ℕ) : ℕ := (kmswStage w e).west e
@[expose] def edgeEast (w : ℕ → Fin 3) (e : ℕ) : ℕ := (kmswStage w e).east e
@[expose] def activeInitial (w : ℕ → Fin 3) (n : ℕ) : ℕ := edgeWest w (act w n)
end DirectedDistances.KMSW
-- Source module DirectedDistances.DirectedPath.Distance
namespace DirectedDistances
open Quiver
universe u v
variable {V : Type u} [Quiver.{v} V] {a b c : V}
noncomputable def sdp (a b : V) : ℕ∞ :=
  ⨅ p : Path a b, (p.length : ℕ∞)
end DirectedDistances
-- Source module DirectedDistances.KMSW.InfiniteGeodesic
namespace DirectedDistances.KMSW
open Quiver
structure PresentVertex (w : ℕ → Fin 3) where
  id : ℕ
  deriving DecidableEq
def EdgePresent (w : ℕ → Fin 3) (e : ℕ) : Prop :=
  ∃ n, e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true
instance presentVertexQuiver (w : ℕ → Fin 3) : Quiver (PresentVertex w) where
  Hom u v := {e : ℕ // EdgePresent w e ∧ edgeWest w e = u.id ∧ edgeEast w e = v.id}
end DirectedDistances.KMSW
-- Source module DirectedDistances.KMSW.BoundaryRecordsMissing
namespace DirectedDistances.KMSW
open scoped Classical
@[expose] def kmswLLCreatedEdge (w : ℕ → Fin 3) (m : ℕ) : ℕ :=
  (kmswStage w m).nextEdge - 1
end DirectedDistances.KMSW
-- Source module DirectedDistances.RandomWalk.IIDVectorWalk
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped BigOperators
@[expose] noncomputable def uniformCodeMeasure : Measure (Fin 3) :=
  Measure.uniformOfFinset Finset.univ
end DirectedDistances.RandomWalk
-- Source module DirectedDistances.KMSW.DirectedContain
namespace DirectedDistances.KMSW
open MeasureTheory
open scoped Classical
structure BoundaryHitWitnesses (w : ℕ → Fin 3) : Prop where
  rightHit : ∀ k : ℤ, 1 ≤ k → ∃ n, R w n = -k
  leftHit : ∀ k : ℤ, k ≤ -1 → ∃ n, L w n = k
@[expose] noncomputable def boundaryHitTime (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ := by
  classical
  by_cases hk0 : k = 0
  · exact 0
  · by_cases hkpos : 0 < k
    · exact Nat.find (h.rightHit k (by omega))
    · exact Nat.find (h.leftHit k (by omega))
@[expose] noncomputable def boundaryVertex (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ := by
  classical
  by_cases hk0 : k = 0
  · exact 0
  · by_cases hk1 : k = 1
    · exact 1
    · exact activeInitial w (boundaryHitTime w h k)
end DirectedDistances.KMSW
-- Source module DirectedDistances.PlanarMap.PermutationSplice
namespace DirectedDistances.PlanarMap
open Equiv
universe u
variable {D : Type u} [DecidableEq D]
@[expose] def insertAfter (σ : Equiv.Perm D) (a x : D) : Equiv.Perm D :=
  σ * Equiv.swap a x
@[expose] def insertBefore (σ : Equiv.Perm D) (a x : D) : Equiv.Perm D :=
  Equiv.swap a x * σ
end DirectedDistances.PlanarMap
-- Source module DirectedDistances.KMSW.StageRotation
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap
abbrev StageDart (k : ℕ) := Fin k × Bool
@[expose] def stageEndpoint (s : State) (d : StageDart s.nextEdge) : ℕ :=
  if d.2 then s.east d.1.val else s.west d.1.val
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
@[expose] def pairSplice {D F : Type*} [DecidableEq D] [DecidableEq F]
    (σ : Equiv.Perm D) (τ : Equiv.Perm F) (a b : D) (x y : F) :
    Equiv.Perm (D ⊕ F) :=
  insertBefore (insertAfter (Equiv.sumCongr σ τ) (.inl a) (.inr x)) (.inl b) (.inr y)
@[expose] def pendant (k : ℕ) (σ : Equiv.Perm (StageDart k)) (A : StageDart k) :
    Equiv.Perm (StageDart (k + 1)) :=
  (allocation k 1).permCongr
    (insertBefore (Equiv.sumCongr σ (Equiv.refl _)) (.inl A) (.inr (0, false)))
@[expose] def leftExisting (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (e A : StageDart k) : Equiv.Perm (StageDart (k + 1)) :=
  (allocation k 1).permCongr
    (pairSplice σ (Equiv.refl _) e A (0, false) (0, true))
@[expose] def leftFresh (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (a A : StageDart k) : Equiv.Perm (StageDart (k + 2)) :=
  (allocation k 2).permCongr
    (pairSplice σ (Equiv.swap (0, false) (1, false)) a A (1, true) (0, true))
@[expose] def up (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (a A : StageDart k) : Equiv.Perm (StageDart (k + 2)) :=
  (allocation k 2).permCongr
    (pairSplice σ (Equiv.swap (0, true) (1, false)) a A (0, false) (1, true))
@[expose] def resize {k l : ℕ} (h : k = l) (σ : Equiv.Perm (StageDart k)) :
    Equiv.Perm (StageDart l) := h ▸ σ
/-- The resize width when the down step allocates one edge. -/
theorem step._proof_5 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .down)
    (hr : s.UR = []) : s.nextEdge + 1 = (kmswStep s c).nextEdge := by
  simp only [kmswStep, hc, kmswStepOfStep, hr, State.addEdge]
/-- The resize width when the down step uses the right boundary. -/
theorem step._proof_6 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .down)
    (head : ℕ) (tail : List ℕ) (hr : s.UR = head :: tail) :
    s.nextEdge = (kmswStep s c).nextEdge := by
  simp only [kmswStep, hc, kmswStepOfStep, hr]
/-- The resize width when the left step starts a fresh boundary. -/
theorem step._proof_7 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .left)
    (hl : s.UL.dropLast.reverse = []) : s.nextEdge + 2 = (kmswStep s c).nextEdge := by
  simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
/-- The resize width when the left step uses the old boundary. -/
theorem step._proof_9 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .left)
    (e : ℕ) (es : List ℕ) (hl : s.UL.dropLast.reverse = e :: es) :
    s.nextEdge + 1 = (kmswStep s c).nextEdge := by
  simp only [kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
/-- The resize width for an up step. -/
theorem step._proof_10 (s : State) (c : Fin 3) (hc : kmswCodeStep c = .up) :
    s.nextEdge + 2 = (kmswStep s c).nextEdge := by
  simp only [kmswStep, hc, kmswStepOfStep, State.addEdge]

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
theorem stageRotation_UL_bound (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e ∈ (kmswStage w n).UL, e < (kmswStage w n).nextEdge := by sorry
end DirectedDistances.KMSW
-- Source module DirectedDistances.KMSW.InfiniteRotation
namespace DirectedDistances.KMSW
@[expose] def kmswVertexComplete (w : ℕ → Fin 3) (n u : ℕ) : Prop :=
  ∀ e, edgeWest w e = u ∨ edgeEast w e = u → e < (kmswStage w n).nextEdge
end DirectedDistances.KMSW
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
theorem kmswInfRot_existsUnique :
    ∃! σ : Equiv.Perm (ℕ × Bool),
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        σ (x.1.val, x.2) = ((stageRot w n x).1.val, (stageRot w n x).2)) ∧
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        σ.symm (x.1.val, x.2) =
          (((stageRot w n).symm x).1.val, ((stageRot w n).symm x).2)) := by sorry
@[expose] noncomputable def kmswInfRot : Equiv.Perm (ℕ × Bool) :=
  (kmswInfRot_existsUnique w hfin).exists.choose
end StageRotationView
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.InfiniteBoundary
namespace DirectedDistances.KMSW
open Filter
open scoped Classical
@[expose] noncomputable def natSelect (P : ℕ → Prop) [DecidablePred P] (i : ℕ) : ℕ :=
  if h : ∃ m, i < Nat.count P (m + 1) then Nat.find h else 0
@[expose] noncomputable def kmswRightBoundaryEdge (w : ℕ → Fin 3) (i : ℕ) : ℕ :=
  act w (natSelect (fun m => ∀ j, j < m → R w m < R w j) i)
end DirectedDistances.KMSW
-- Source module DirectedDistances.KMSW.BusemannUIQBOT
namespace DirectedDistances.KMSW
open Quiver MeasureTheory DirectedDistances.RandomWalk
open scoped Classical
noncomputable def presentLdp {w : ℕ → Fin 3} (x z : PresentVertex w) : WithBot ℕ∞ :=
  ⨆ p : Path x z, ((p.length : ℕ∞) : WithBot ℕ∞)
end DirectedDistances.KMSW
-- Source module DirectedDistances.KMSW.BusemannBoundaryM0
namespace DirectedDistances.KMSW
open Quiver
noncomputable def boundaryPresentVertex (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ) :
    PresentVertex w :=
  ⟨boundaryVertex w h k⟩
end DirectedDistances.KMSW
-- Source module DirectedDistances.KMSW.KMSWFutureMapCarrier
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap Quiver
@[expose] def futureMapRootDart : ℕ × Bool := (0, false)
end DirectedDistances.KMSW
-- Source module DirectedDistances.KMSW.KMSWWindowPatchTriangles
namespace DirectedDistances.KMSW
structure KMSWWindowPatchData where
  φ : ℕ → ℕ
  A : List ℕ
  B : List ℕ
  YL : List ℕ
  YR : List ℕ
  XL : List ℕ
  XR : List ℕ
end DirectedDistances.KMSW
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
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
-- Source module DirectedDistances.KMSW.KMSWWindowPatchVertex
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
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWindowInfiniteMaps
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def kmswWindowEdgeMapInf (w : ℕ → Fin 3) (s e : ℕ) : ℕ :=
  (kmswWindowPatchData w s e).φ e
@[expose] def kmswWindowVertexMapInf (w : ℕ → Fin 3) (s v : ℕ) : ℕ :=
  kmswWindowPatchVertexMap w s (4 * v + 1) v
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWholePlaneColimit
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def shiftedStream (W : ℤ → Fin 3) (N : ℕ) : ℕ → Fin 3 :=
  fun i => W ((i : ℤ) - N)
@[expose] def wholePlaneEdgeTrans (W : ℤ → Fin 3) (N N' : ℕ) (_h : N ≤ N') :
    ℕ → ℕ :=
  kmswWindowEdgeMapInf (shiftedStream W N') (N' - N)
@[expose] def wholePlaneVertexTrans (W : ℤ → Fin 3) (N N' : ℕ) (_h : N ≤ N') :
    ℕ → ℕ :=
  kmswWindowVertexMapInf (shiftedStream W N') (N' - N)
@[expose] def wholePlaneEdgeRel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) : Prop :=
  ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M,
    wholePlaneEdgeTrans W a.1 M ha a.2 = wholePlaneEdgeTrans W b.1 M hb b.2
@[expose] def wholePlaneVertexRel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) : Prop :=
  ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M,
    wholePlaneVertexTrans W a.1 M ha a.2 = wholePlaneVertexTrans W b.1 M hb b.2
theorem wholePlaneEdgeRel_equivalence (W : ℤ → Fin 3) :
    Equivalence (wholePlaneEdgeRel W) := by sorry
theorem wholePlaneVertexRel_equivalence (W : ℤ → Fin 3) :
    Equivalence (wholePlaneVertexRel W) := by sorry
@[expose] def wholePlaneEdgeSetoid (W : ℤ → Fin 3) : Setoid (Σ _ : ℕ, ℕ) where
  r := wholePlaneEdgeRel W
  iseqv := wholePlaneEdgeRel_equivalence W
@[expose] def wholePlaneVertexSetoid (W : ℤ → Fin 3) : Setoid (Σ _ : ℕ, ℕ) where
  r := wholePlaneVertexRel W
  iseqv := wholePlaneVertexRel_equivalence W
@[expose] def WholePlaneEdge (W : ℤ → Fin 3) : Type :=
  Quotient (wholePlaneEdgeSetoid W)
@[expose] def WholePlaneVertex (W : ℤ → Fin 3) : Type :=
  Quotient (wholePlaneVertexSetoid W)
@[expose] def wholePlaneEdgeι (W : ℤ → Fin 3) (N : ℕ) (e : ℕ) : WholePlaneEdge W :=
  Quotient.mk (wholePlaneEdgeSetoid W) ⟨N, e⟩
@[expose] def wholePlaneVertexι (W : ℤ → Fin 3) (N : ℕ) (v : ℕ) : WholePlaneVertex W :=
  Quotient.mk (wholePlaneVertexSetoid W) ⟨N, v⟩
theorem wholePlaneEdgeRel_west (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    wholePlaneVertexι W a.1 (edgeWest (shiftedStream W a.1) a.2) =
      wholePlaneVertexι W b.1 (edgeWest (shiftedStream W b.1) b.2) := by sorry
theorem wholePlaneEdgeRel_east (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    wholePlaneVertexι W a.1 (edgeEast (shiftedStream W a.1) a.2) =
      wholePlaneVertexι W b.1 (edgeEast (shiftedStream W b.1) b.2) := by sorry
@[expose] def wholePlaneEdgeWest (W : ℤ → Fin 3) : WholePlaneEdge W → WholePlaneVertex W :=
  Quotient.lift (fun a => wholePlaneVertexι W a.1 (edgeWest (shiftedStream W a.1) a.2))
    (wholePlaneEdgeRel_west W)
@[expose] def wholePlaneEdgeEast (W : ℤ → Fin 3) : WholePlaneEdge W → WholePlaneVertex W :=
  Quotient.lift (fun a => wholePlaneVertexι W a.1 (edgeEast (shiftedStream W a.1) a.2))
    (wholePlaneEdgeRel_east W)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWholePlaneRotationTransport
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def KMSWFiniteIncidence (w : ℕ → Fin 3) : Prop :=
  ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite
@[expose] def wholePlaneFresh (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (v : ℕ) : Prop :=
  (kmswStage (shiftedStream W N') (N' - N)).nextVertex ≤
    wholePlaneVertexTrans W N N' h v
@[expose] def WholePlaneRotationHypothesis (W : ℤ → Fin 3) : Prop :=
  (∀ N, KMSWFiniteIncidence (shiftedStream W N)) ∧
  (∀ N v, ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
    wholePlaneFresh W M M' hMM' (wholePlaneVertexTrans W N M hNM v))
@[expose] def wholePlaneDartTrans (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (d : ℕ × Bool) : ℕ × Bool :=
  (wholePlaneEdgeTrans W N N' h d.1, d.2)
@[expose] def wholePlaneDartι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    WholePlaneEdge W × Bool :=
  (wholePlaneEdgeι W N d.1, d.2)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWholePlaneRotation
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def WholePlaneDart (W : ℤ → Fin 3) : Type := WholePlaneEdge W × Bool
@[expose] noncomputable def runRot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) :
    Equiv.Perm (ℕ × Bool) :=
  if inv then (kmswInfRot (shiftedStream W N) (H.1 N)).symm
  else kmswInfRot (shiftedStream W N) (H.1 N)
@[expose] def eventualValue (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) (d : ℕ × Bool) (y : WholePlaneDart W) : Prop :=
  ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
    wholePlaneDartι W M' (runRot W H inv M'
      (wholePlaneDartTrans W N M' (hNM.trans hMM') d)) = y
theorem eventualValue_existsUnique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    ∃! y, eventualValue W H inv N d y := by sorry
@[expose] noncomputable def value (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    WholePlaneDart W :=
  (eventualValue_existsUnique W H inv N d).exists.choose
theorem value_rel (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneEdgeRel W a b) (s : Bool) :
    value W H inv a.1 (a.2, s) = value W H inv b.1 (b.2, s) := by sorry
@[expose] noncomputable def wholePlaneRot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : WholePlaneDart W → WholePlaneDart W :=
  fun x => Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    Classical.choose (show ∃ y : WholePlaneDart W,
      ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
        wholePlaneDartι W L (kmswInfRot (shiftedStream W L) (H.1 L)
          (wholePlaneDartTrans W a.1 L (hNM.trans hML) (a.2, x.2))) = y from by
            exact (eventualValue_existsUnique W H false a.1 (a.2, x.2)).exists))
    (by
      intro a b hab
      exact value_rel W H false a b hab x.2) x.1
@[expose] noncomputable def wholePlaneRotInv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : WholePlaneDart W → WholePlaneDart W :=
  fun x => Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    Classical.choose (show ∃ y : WholePlaneDart W,
      ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
        wholePlaneDartι W L ((kmswInfRot (shiftedStream W L) (H.1 L)).symm
          (wholePlaneDartTrans W a.1 L (hNM.trans hML) (a.2, x.2))) = y from by
            exact (eventualValue_existsUnique W H true a.1 (a.2, x.2)).exists))
    (by
      intro a b hab
      exact value_rel W H true a b hab x.2) x.1
theorem wholePlaneRot_comp_inv (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) :
    wholePlaneRot W H ∘ wholePlaneRotInv W H = id := by sorry
theorem wholePlaneRotInv_comp_rot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    wholePlaneRotInv W H ∘ wholePlaneRot W H = id := by sorry
@[expose] noncomputable def wholePlaneRotation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Equiv.Perm (WholePlaneDart W) where
  toFun := wholePlaneRot W H
  invFun := wholePlaneRotInv W H
  left_inv := congrFun (wholePlaneRotInv_comp_rot W H)
  right_inv := congrFun (wholePlaneRot_comp_inv W H)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWholePlaneFaces
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def wholePlaneDartFlip (W : ℤ → Fin 3) : Equiv.Perm (WholePlaneDart W) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl
@[expose] noncomputable def wholePlaneFaceSucc (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Equiv.Perm (WholePlaneDart W) :=
  (wholePlaneRotation W H).symm * wholePlaneDartFlip W
@[expose] def eventualPresence (W : ℤ → Fin 3) (N e : ℕ) : Prop :=
  ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
    EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W N L (hNM.trans hML) e)
theorem eventualPresence_rel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    eventualPresence W a.1 a.2 = eventualPresence W b.1 b.2 := by sorry
@[expose] def wholePlaneEdgePresent (W : ℤ → Fin 3) : WholePlaneEdge W → Prop :=
  Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
      EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W a.1 L (hNM.trans hML) a.2))
    (by
      intro a b hab
      exact eventualPresence_rel W a b hab)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure
namespace DLQG1.Palomar.Model.RandomWalk
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
@[expose] noncomputable def wholePlaneIIDCodeMeasure : Measure (ℤ → Fin 3) :=
  Measure.infinitePi (fun _ : ℤ => uniformCodeMeasure)
end DLQG1.Palomar.Model.RandomWalk
-- Source module DirectedDistances.KMSW.WholePlaneRightBoundary
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open MeasureTheory RandomWalk
@[expose] def wholePlaneRightmostOutgoingAt (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    (e : WholePlaneEdge W) : Prop :=
  wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v ∧
    ∃ k : ℕ, 0 < k ∧
      (((wholePlaneRotation W H).symm ^ k) (e, false)).2 = true ∧
      wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ k) (e, false)).1 ∧
      ∀ j : ℕ, 0 < j → j < k →
        ¬ wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ j) (e, false)).1
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.WholePlaneDrawingCombinatorics
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
@[expose] def wholePlaneDartVertex (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.BoundaryLabelling
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open scoped Classical
@[expose] noncomputable def boundaryOuterEdge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ :=
  if k ≤ -1 then kmswLLCreatedEdge w (boundaryHitTime w h k)
  else if 1 ≤ k then kmswRightBoundaryEdge w k.toNat
  else 0
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.WholePlaneRootedMapFields
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open Quiver
@[expose] def wholePlaneDartTail (W : ℤ → Fin 3) : WholePlaneDart W → Prop :=
  fun d => ¬ d.2 ∧ wholePlaneEdgePresent W d.1
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutRootTransport
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
@[expose] def m0CutLambdaZero (W : ℤ → Fin 3) : WholePlaneEdge W :=
  wholePlaneEdgeι W 0 0
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.WholePlaneRightmostRays
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
structure WholePlaneRightmostRay (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) where
  vertex : ℕ → WholePlaneVertex W
  edge : ℕ → WholePlaneEdge W
  rightmost : ∀ i, wholePlaneRightmostOutgoingAt W H (vertex i) (edge i)
  target : ∀ i, wholePlaneEdgeEast W (edge i) = vertex (i + 1)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.WholePlaneLeftmostIncoming
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def wholePlaneLeftmostIncomingAt (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    (e : WholePlaneEdge W) : Prop :=
  wholePlaneEdgePresent W e ∧ wholePlaneEdgeEast W e = v ∧
    ∃ k : ℕ, 0 < k ∧
      (((wholePlaneRotation W H).symm ^ k) (e, true)).2 = false ∧
      wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ k) (e, true)).1 ∧
      ∀ j : ℕ, 0 < j → j < k →
        ¬ wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ j) (e, true)).1
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutSeam
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
structure M0CutLeftmostChain (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) where
  vertex : ℕ → WholePlaneVertex W
  edge : ℕ → WholePlaneEdge W
  endpoint : vertex 0 = v
  leftmost : ∀ i, wholePlaneLeftmostIncomingAt W H (vertex i) (edge i)
  westEndpoint : ∀ i, wholePlaneEdgeWest W (edge i) = vertex (i + 1)
@[expose] def m0CutSeamEdge (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (e : WholePlaneEdge W) : Prop :=
  e = m0CutLambdaZero W ∨
    (∃ P : WholePlaneRightmostRay W H,
      P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W) ∧
        ∃ j, P.edge j = e) ∨
    ∃ P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)),
      ∃ j, P.edge j = e
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutLeftSide
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
@[expose] def m0CutLeftStep (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (S : WholePlaneEdge W → Prop) (d e : WholePlaneDart W) : Prop :=
  e = wholePlaneFaceSucc W H d ∨ (e = wholePlaneDartFlip W d ∧ ¬ S d.1)
@[expose] def m0CutLeftDarts (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (S : WholePlaneEdge W → Prop) : Set (WholePlaneDart W) :=
  {d | ∃ e, S e ∧ Relation.ReflTransGen (m0CutLeftStep W H S) (e, false) d}
@[expose] def m0CutLeftEdges (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (S : WholePlaneEdge W → Prop) : Set (WholePlaneEdge W) :=
  Prod.fst '' m0CutLeftDarts W H S
@[expose] def m0CutLeftVertices (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (S : WholePlaneEdge W → Prop) : Set (WholePlaneVertex W) :=
  wholePlaneDartVertex W '' m0CutLeftDarts W H S
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutPresence
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open Quiver
@[expose] def m0CutMissing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (E : WholePlaneEdge W) : Prop :=
  (∃ P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)),
    ∃ j, P.edge j = E) ∨ ¬ wholePlaneEdgePresent W E
@[expose] def m0CutTail (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : WholePlaneDart W) : Prop :=
  wholePlaneDartTail W d ∧ ¬ m0CutMissing W H d.1
@[expose] def m0CutDirectedStep (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
    (u v : WholePlaneVertex W) : Prop :=
  ∃ d : WholePlaneDart W, m0CutTail W H d ∧ d.1 ∈ m0CutLeftEdges W H S ∧
    wholePlaneEdgeWest W d.1 = u ∧ wholePlaneEdgeEast W d.1 = v
section Paths
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
@[expose] def m0CutReachableLength {V : Type*} (R : V → V → Prop) :
    ℕ → V → V → Prop
  | 0, u, v => u = v
  | n + 1, u, v => ∃ x, m0CutReachableLength R n u x ∧ R x v
@[expose] noncomputable def m0CutSDP (u v : WholePlaneVertex W) : ℕ∞ :=
  ⨅ n : ℕ, ⨅ (_ : m0CutReachableLength (m0CutDirectedStep W H S) n u v), (n : ℕ∞)
@[expose] noncomputable def m0CutLDP (u v : WholePlaneVertex W) : WithBot ℕ∞ :=
  ⨆ n : ℕ, ⨆ (_ : m0CutReachableLength (m0CutDirectedStep W H S) n u v),
    ((n : ℕ∞) : WithBot ℕ∞)
end Paths
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutData
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
structure M0CutData (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) where
  betaR : WholePlaneRightmostRay W H
  betaR_start : betaR.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W)
  betaL : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W))
namespace M0CutData
variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
@[expose] def seam (_D : M0CutData W H) : WholePlaneEdge W → Prop :=
  m0CutSeamEdge W H
@[expose] def missing (_D : M0CutData W H) : WholePlaneEdge W → Prop :=
  m0CutMissing W H
@[expose] def tail (_D : M0CutData W H) : WholePlaneDart W → Prop :=
  m0CutTail W H
@[expose] def rootDart (_D : M0CutData W H) : WholePlaneDart W :=
  (m0CutLambdaZero W, false)
@[expose] def x (D : M0CutData W H) (k : ℤ) : WholePlaneVertex W :=
  if k = 0 then wholePlaneEdgeWest W (m0CutLambdaZero W)
  else if k = 1 then wholePlaneEdgeEast W (m0CutLambdaZero W)
  else if 2 ≤ k then D.betaR.vertex (k - 1).toNat
  else D.betaL.vertex (-k).toNat
@[expose] noncomputable def sdp (D : M0CutData W H) :
    WholePlaneVertex W → WholePlaneVertex W → ℕ∞ :=
  m0CutSDP W H D.seam
@[expose] noncomputable def ldp (D : M0CutData W H) :
    WholePlaneVertex W → WholePlaneVertex W → WithBot ℕ∞ :=
  m0CutLDP W H D.seam
end M0CutData
theorem m0CutData_nonempty (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    Nonempty (M0CutData W H) := by sorry
@[expose] noncomputable def m0CutData (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) : M0CutData W H :=
  Classical.choice (m0CutData_nonempty W H h hLL)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutBusemann
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open Quiver
@[expose] def m0CutReachable (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
    (u v : WholePlaneVertex W) : Prop :=
  ∃ n, m0CutReachableLength (m0CutDirectedStep W H S) n u v
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.PaperProofs.Section1.BusemannM0Identified
namespace DLQG1.Palomar.Model.PaperProofs.Section1
open MeasureTheory DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW (BoundaryHitWitnesses kmswLLCreatedEdge boundaryHitTime
  boundaryVertex futureMapRootDart EdgePresent edgeWest edgeEast PresentVertex
  presentLdp boundaryPresentVertex)
@[expose] def IsIdentifiedM0BusemannSDP {W : ℤ → Fin 3}
    {H : WholePlaneRotationHypothesis W} (D : M0CutData W H) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → WholePlaneVertex W, Function.Injective y →
      (∀ j, m0CutReachable W H D.seam (D.x k) (y j) ∧
        m0CutReachable W H D.seam (D.x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
        X k' - X k =
          ((D.sdp (D.x k') (y j)).toNat : ℤ) -
            ((D.sdp (D.x k) (y j)).toNat : ℤ)
@[expose] def IsIdentifiedM0BusemannLDP {W : ℤ → Fin 3}
    {H : WholePlaneRotationHypothesis W} (D : M0CutData W H) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → WholePlaneVertex W, Function.Injective y →
      (∀ j, m0CutReachable W H D.seam (D.x k) (y j) ∧
        m0CutReachable W H D.seam (D.x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
        ∃ n n' : ℕ,
          D.ldp (D.x k') (y j) = ((n : ℕ∞) : WithBot ℕ∞) ∧
          D.ldp (D.x k) (y j) = ((n' : ℕ∞) : WithBot ℕ∞) ∧
          X k' - X k = (n : ℤ) - (n' : ℤ)
end DLQG1.Palomar.Model.PaperProofs.Section1
-- Source module DirectedDistances.Paper.Section1.BusemannM0
namespace DLQG1.Palomar.Principal
open DirectedDistances
open MeasureTheory DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW (BoundaryHitWitnesses kmswLLCreatedEdge boundaryHitTime
  boundaryVertex futureMapRootDart EdgePresent edgeWest edgeEast PresentVertex
  presentLdp boundaryPresentVertex)
open DLQG1.Palomar.Model.PaperProofs.Section1
end DLQG1.Palomar.Principal
-- Source module DirectedDistances.KMSW.ShiftInfRotFirstReturn
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def endpoint (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1
end DLQG1.Palomar.Model.KMSW

-- Source-backed model witnesses and whole-carrier chooser definitions for Theorems 1.7 and 1.8.
namespace DLQG1.Palomar.Model.PaperProofs.Section7
abbrev identifiedLDPWitness (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W,
    ∃ h : DirectedDistances.KMSW.BoundaryHitWitnesses
      (DLQG1.Palomar.Model.KMSW.shiftedStream W 0),
    ∃ hLL : ∀ k : ℤ, k ≤ 0 →
      DLQG1.Palomar.Model.KMSW.wholePlaneEdgePresent W
        (DLQG1.Palomar.Model.KMSW.wholePlaneEdgeι W 0
          (DirectedDistances.KMSW.kmswLLCreatedEdge
            (DLQG1.Palomar.Model.KMSW.shiftedStream W 0)
            (DirectedDistances.KMSW.boundaryHitTime
              (DLQG1.Palomar.Model.KMSW.shiftedStream W 0) h (k - 1)))),
    DLQG1.Palomar.Model.PaperProofs.Section1.IsIdentifiedM0BusemannLDP
      (DLQG1.Palomar.Model.KMSW.m0CutData W H h hLL) X
abbrev identifiedSDPWitness (W : ℤ → Fin 3) (X : ℤ → ℤ) : Prop :=
  ∃ H : DLQG1.Palomar.Model.KMSW.WholePlaneRotationHypothesis W,
    ∃ h : DirectedDistances.KMSW.BoundaryHitWitnesses
      (DLQG1.Palomar.Model.KMSW.shiftedStream W 0),
    ∃ hLL : ∀ k : ℤ, k ≤ 0 →
      DLQG1.Palomar.Model.KMSW.wholePlaneEdgePresent W
        (DLQG1.Palomar.Model.KMSW.wholePlaneEdgeι W 0
          (DirectedDistances.KMSW.kmswLLCreatedEdge
            (DLQG1.Palomar.Model.KMSW.shiftedStream W 0)
            (DirectedDistances.KMSW.boundaryHitTime
              (DLQG1.Palomar.Model.KMSW.shiftedStream W 0) h (k - 1)))),
    DLQG1.Palomar.Model.PaperProofs.Section1.IsIdentifiedM0BusemannSDP
      (DLQG1.Palomar.Model.KMSW.m0CutData W H h hLL) X
@[expose] noncomputable def identifiedLDPBusemann (W : ℤ → Fin 3) : ℤ → ℤ := by
  classical
  exact if hW : ∃ X : ℤ → ℤ, identifiedLDPWitness W X then hW.choose else fun _ => 0
@[expose] noncomputable def identifiedSDPBusemann (W : ℤ → Fin 3) : ℤ → ℤ := by
  classical
  exact if hW : ∃ X : ℤ → ℤ, identifiedSDPWitness W X then hW.choose else fun _ => 0
end DLQG1.Palomar.Model.PaperProofs.Section7

namespace DLQG1.Palomar.Principal
open MeasureTheory ProbabilityTheory Filter Asymptotics
theorem busemann_increments :
(
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPWitness W (DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W)) ∧
    iIndepFun (fun k W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W 1 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (1 - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W 0 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (0 - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1) ≤ -1) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W (k - 1) - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedLDPBusemann W k)
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure)) ∧
    (
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure,
      DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPWitness W (DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W)) ∧
    iIndepFun (fun k W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W 1 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (1 - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W 0 - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (0 - 1))
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      -1 ≤ DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1)) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1))
      (fun W => DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W (k - 1) - DLQG1.Palomar.Model.PaperProofs.Section7.identifiedSDPBusemann W k)
      DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure)) := by
  sorry
end DLQG1.Palomar.Principal
end BusemannInterface
