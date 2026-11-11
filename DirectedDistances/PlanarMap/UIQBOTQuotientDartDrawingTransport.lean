/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.ExternalFaceIntervalOrder2
public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation11

/-! # UIQBOT quotient-dart drawing transport

Helper toward Definition 3.2: transport the KMSW labelled darts to the
canonical quotient-geometric-edge dart carrier. The quotient representative's
bit determines the adjustment between the two traversal conventions. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW DirectedDistances.PaperProofs.Section4

/-- Helper toward Definition 3.2: adjust a directed traversal bit by the bit
of the chosen quotient representative. -/
@[expose] def uiqbotQuotientDartBit (repBit traversalBit : Bool) : Bool :=
  if repBit then traversalBit else !traversalBit

/-- Helper toward Definition 3.2: the KMSW labelled dart represented by a
quotient dart, with orientation adjusted by the quotient representative. -/
@[expose] def uiqbotQuotientDartMap
    {D : Type*} (iota : ℕ ≃ D) (repBit : D → Bool)
    (d : D × Bool) : ℕ × Bool :=
  (iota.symm d.1, uiqbotQuotientDartBit (repBit d.1) d.2)

/-- Helper toward Definition 3.2: the quotient-dart and KMSW-dart carriers
are equivalent, including the representative-dependent traversal bit. -/
@[expose] def uiqbotQuotientDartEquiv
    {D : Type*} (iota : ℕ ≃ D) (repBit : D → Bool) : D × Bool ≃ ℕ × Bool where
  toFun := uiqbotQuotientDartMap iota repBit
  invFun d := (iota d.1,
    uiqbotQuotientDartBit (repBit (iota d.1)) d.2)
  left_inv d := by
    rcases d with ⟨q, b⟩
    simp only [uiqbotQuotientDartMap, Equiv.apply_symm_apply]
    cases repBit q <;> cases b <;> rfl
  right_inv d := by
    rcases d with ⟨e, b⟩
    simp only [uiqbotQuotientDartMap, Equiv.symm_apply_apply]
    cases repBit (iota e) <;> cases b <;> rfl

/-- Helper toward Definition 3.2: the canonical KMSW quotient-dart
equivalence uses the selected quotient representative's traversal bit. -/
@[expose] def uiqbotKMSWQuotientDartEquiv
    {w : ℕ → Fin 3}
    {hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (iota : ℕ ≃ P.GeometricEdge) : P.GeometricEdge × Bool ≃ ℕ × Bool :=
  uiqbotQuotientDartEquiv iota (fun q => q.out.2)

/-- Helper toward Definition 3.2: the quotient-dart equivalence respects dart
reversal, with the source and target bit conventions accounted for. -/
theorem uiqbotKMSWQuotientDartEquiv_flip
    {w : ℕ → Fin 3}
    {hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (iota : ℕ ≃ P.GeometricEdge) (d : P.GeometricEdge × Bool) :
    uiqbotKMSWQuotientDartEquiv P iota (d.1, !d.2) =
      ((uiqbotKMSWQuotientDartEquiv P iota d).1,
        !(uiqbotKMSWQuotientDartEquiv P iota d).2) := by
  rcases d with ⟨q, b⟩
  cases h : q.out.2 <;> cases b <;>
    simp [uiqbotKMSWQuotientDartEquiv, uiqbotQuotientDartEquiv,
      uiqbotQuotientDartMap, uiqbotQuotientDartBit, h]

/-- Helper toward Definition 3.2: a quotient dart in the directed orientation
maps to the west-to-east KMSW dart, regardless of its chosen representative. -/
theorem uiqbotKMSWQuotientDartEquiv_directed
    {w : ℕ → Fin 3}
    {hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (iota : ℕ ≃ P.GeometricEdge) (e : ℕ) :
    uiqbotKMSWQuotientDartEquiv P iota
      (iota e, !(iota e).out.2) = (e, false) := by
  simp [uiqbotKMSWQuotientDartEquiv, uiqbotQuotientDartEquiv,
    uiqbotQuotientDartMap, uiqbotQuotientDartBit]

/-- Helper toward Definition 3.2: the quotient dart in reverse directed
orientation maps to the east-to-west KMSW dart. -/
theorem uiqbotKMSWQuotientDartEquiv_reverseDirected
    {w : ℕ → Fin 3}
    {hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite}
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (iota : ℕ ≃ P.GeometricEdge) (e : ℕ) :
    uiqbotKMSWQuotientDartEquiv P iota
      (iota e, (iota e).out.2) = (e, true) := by
  simp [uiqbotKMSWQuotientDartEquiv, uiqbotQuotientDartEquiv,
    uiqbotQuotientDartMap, uiqbotQuotientDartBit]

/-- Helper toward Definition 3.2: conjugate the rotation of a labelled-dart
drawing onto an equivalent dart carrier. -/
@[expose] def uiqbotTransportRotation
    {D E : Type*} (f : D ≃ E) (rot : Equiv.Perm E) : Equiv.Perm D where
  toFun d := f.symm (rot (f d))
  invFun d := f.symm (rot.symm (f d))
  left_inv d := by simp
  right_inv d := by simp

/-- Helper toward Definition 3.2: the geometric-successor equation transports
through a dart equivalence that commutes with reversal. -/
theorem uiqbotTransportRotation_geometricSucc
    {D E : Type*} (f : D ≃ E) (rot : Equiv.Perm E)
    (flipD : D → D) (flipE : E → E)
    (hflip : ∀ d, f (flipD d) = flipE (f d)) (d : D) :
    (uiqbotTransportRotation f rot).symm (flipD d) =
      f.symm (rot.symm (flipE (f d))) := by
  simp [uiqbotTransportRotation, hflip]

/-- Helper toward Definition 3.2: the canonical presentation satisfies the
upper-left side predicate. -/
theorem uiqbotCanonicalBoundaryPresentation_ulOkInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    ULOkInf (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) :=
  DirectedDistances.PaperProofs.Section4.uiqbotCanonicalBoundaryPresentation_ulOkInf
    w hfin htrans hR hL0

/-- Helper toward Definition 3.2: the canonical presentation satisfies the
lower-right side predicate. -/
theorem uiqbotCanonicalBoundaryPresentation_lrOkInf
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    LROkInf (uiqbotCanonicalBoundaryPresentation w hfin htrans hR hL0) :=
  DirectedDistances.PaperProofs.Section4.uiqbotCanonicalBoundaryPresentation_lrOkInf
    w hfin htrans hR hL0







































































end DirectedDistances.PlanarMap

end
