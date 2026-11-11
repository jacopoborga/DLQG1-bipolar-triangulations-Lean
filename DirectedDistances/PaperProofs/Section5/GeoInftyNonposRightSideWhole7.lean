/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole6
import DirectedDistances.KMSW.KMSWWindowDeterminism

/-! Transport of the code-built nonpositive right side across a shared stopping
frontier. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical
universe u

/-- Helper toward Lemma 5.5: two stopped prefix streams with the same finite
boundary frontier have equal KMSW states, by the exact prefix-dependence
theorem `kmswStage_eq_of_prefix`. -/
theorem kmswStage_eq_of_sharedBoundaryStoppingFrontier
    (k : ℤ) (u v : ℕ → Fin 3) (n : ℕ)
    (hstopU : boundaryCodeStoppingTime k (rMinusPrefixPath u) = n)
    (hp : ∀ i < n, u i = v i) :
    boundaryCodeStoppingTime k (rMinusPrefixPath v) = n ∧
      kmswStage u n = kmswStage v n := by
  constructor
  · apply rMinus_boundaryCodeStoppingTime_eq_of_prefix n k
      (rMinusPrefixPath u) (rMinusPrefixPath v) hstopU
    intro i hi
    simpa [rMinusPrefixPath] using hp i hi
  · exact kmswStage_eq_of_prefix u v n hp

/-- Helper toward Lemma 5.5: equality of types induces the equivalence given
by transport in both directions. -/
@[expose] def transportEquivOfTypeEq {α β : Type u} (h : α = β) : α ≃ β where
  toFun := Eq.mp h
  invFun := Eq.mpr h
  left_inv := by intro a; cases h; rfl
  right_inv := by intro b; cases h; rfl

/-- Helper toward Lemma 5.5: equal input prefixes transport the quotient
dart carrier along the proved equality of finite KMSW states. -/
@[expose] def rMinusCodeGluedDartEquiv_of_sharedPrefix
    (M : GeometricSideSubmap) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i) :
    RMinusCodeGluedDart (kmswStage u n) M ≃
      RMinusCodeGluedDart (kmswStage v n) M :=
  transportEquivOfTypeEq
    (congrArg (fun F : State => RMinusCodeGluedDart F M)
      (kmswStage_eq_of_prefix u v n hp))

/-- Helper toward Lemma 5.5: equal input prefixes transport the quotient
vertex carrier along the proved equality of finite KMSW states. -/
@[expose] def rMinusCodeGluedVertexEquiv_of_sharedPrefix
    (M : GeometricSideSubmap) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i) :
    {z : RMinusCodeRawVertex (kmswStage u n) M //
      z ∈ RMinusCodeGluedVertex (kmswStage u n) M} ≃
    {z : RMinusCodeRawVertex (kmswStage v n) M //
      z ∈ RMinusCodeGluedVertex (kmswStage v n) M} :=
  transportEquivOfTypeEq
    (congrArg (fun F : State =>
      {z : RMinusCodeRawVertex F M // z ∈ RMinusCodeGluedVertex F M})
      (kmswStage_eq_of_prefix u v n hp))

/-- Helper toward Lemma 5.5: transporting a stage dart across an equality of
edge counts is the identity on its edge label and side bit. -/
private theorem stageDart_eq_mp_apply {m n : ℕ} (h : m = n)
    (d : StageDart m) :
    Eq.mp (congrArg StageDart h) d = (Fin.cast h d.1, d.2) := by
  cases h
  rfl

/-- Helper toward Lemma 5.5: the finite rotation conjugacy supplied by the
stage-map isomorphism is exactly transport along the state equality. -/
theorem stageRot_cast_conj_of_prefix {u v : ℕ → Fin 3} (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (d : StageDart (kmswStage u n).nextEdge) :
    Eq.mp (congrArg StageDart
      (congrArg (fun s : State => s.nextEdge)
        (kmswStage_eq_of_prefix u v n hp))) (stageRot u n d) =
      stageRot v n (Eq.mp (congrArg StageDart
        (congrArg (fun s : State => s.nextEdge)
          (kmswStage_eq_of_prefix u v n hp))) d) := by
  let hnext := congrArg (fun s : State => s.nextEdge)
    (kmswStage_eq_of_prefix u v n hp)
  have h := stageRot_comm_of_prefix n hp d
  change (kmswStageDirectedMapIsoOfPrefix u v n hp).toEquiv
      (stageRot u n d) = stageRot v n
        ((kmswStageDirectedMapIsoOfPrefix u v n hp).toEquiv d) at h
  rw [kmswStageDirectedMapIsoOfPrefix_apply u v n hp
    (stageRot u n d).1 (stageRot u n d).2,
    kmswStageDirectedMapIsoOfPrefix_apply u v n hp d.1 d.2] at h
  change Eq.mp (congrArg StageDart hnext) (stageRot u n d) =
    stageRot v n (Eq.mp (congrArg StageDart hnext) d)
  rw [stageDart_eq_mp_apply hnext (stageRot u n d),
    stageDart_eq_mp_apply hnext d]
  exact h


















































end DirectedDistances.PaperProofs.Section5
