module

public import DirectedDistances.KMSW.InftyCutP3
public import DirectedDistances.KMSW.BusemannM0OnePremise

/-! # Conditional reduction from the open P1 family

This module reduces the iid-code `M_{0,∞}` Busemann conclusions of
conditional reduction: the only remaining premise is
`CutWindowP1Family` almost surely. This is NOT `thm-busemann`. -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory

/-- The open M-hat/shift content of `lem-quad-kmsw`
This is the P1 premise, stated for one code sequence; it is open and is not
proved here. -/
@[expose] def CutWindowP1Family (ω : ℕ → Fin 3) : Prop :=
  ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
    ∃ f : ∀ K : ℕ,
      PresentVertex (cutWindowRPhaseCodes ω h K) ↪
        PresentVertex (fun i => ω (i + 1)),
      (∀ (K : ℕ) (z : PresentVertex (fun i => ω (i + 1))),
        (∃ r : Path
          (⟨boundaryVertex (fun i => ω (i + 1)) h (-(K : ℤ))⟩ :
            PresentVertex (fun i => ω (i + 1))) z,
          ∀ e ∈ pathEdgeList r,
            ∀ he : EdgePresent (fun i => ω (i + 1)) e,
              boundaryHitTime (fun i => ω (i + 1)) h (-(K : ℤ)) ≤
                actTime (fun i => ω (i + 1)) e he) →
        ∃ b : PresentVertex (cutWindowRPhaseCodes ω h K),
          f K b = z ∧
            ∃ N, b.id < (kmswStage (cutWindowRPhaseCodes ω h K) N).nextVertex) ∧
      (∀ (K : ℕ) (i : ℕ),
        i ∈ cutWindowP3AllocatedIds (cutWindowRPhaseCodes ω h K)
          (fun i => ω (i + 1)) (f K) h K →
        ∀ {v} (q : Path
          (f K (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K))) v),
          (∀ e ∈ pathEdgeList q,
            e ∈ cutWindowP3Region (fun i => ω (i + 1)) h K) →
          ∃ b : PresentVertex (cutWindowRPhaseCodes ω h K),
            ∃ r : Path (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) b,
              f K b = v ∧ ∀ y ∈ r.vertices, f K y ∈ q.vertices)

/-- Conditional reduction for the SDP conclusions of `thm-busemann`
`CutWindowP1Family` almost surely; this is NOT `thm-busemann`. -/
theorem iidCodes_ae_boundaryBusemannSDP_of_P1
    (hP1 : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, CutWindowP1Family ω) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannSDP
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) ∧
          (∀ l k : ℤ, 0 ≤ l → l < k →
            X l - X k ≤
              ((sdp (boundaryPresentVertex (fun i => ω (i + 1)) h l)
                (boundaryPresentVertex (fun i => ω (i + 1)) h k)).toNat : ℤ)) ∧
          (∀ k : ℤ, 1 ≤ k → -1 ≤ X k - X (k - 1)) := by
  have hAvoid := ae_cutWindow_finiteAvoidance_of_P1 hP1
  filter_upwards [hP1, hAvoid,
    iidCodes_ae_boundaryBusemannSDP_of_windowFiniteAvoidance]
    with ω _ hωAvoid hωBusemann
  obtain ⟨h, hBusemann⟩ := hωBusemann
  obtain ⟨X, hX, hUnique, hTriangle, hIncrement⟩ := hBusemann (hωAvoid h)
  exact ⟨h, X, hX, hUnique, hTriangle, hIncrement⟩

/-- Conditional reduction for the LDP conclusions of `thm-busemann`
`CutWindowP1Family` almost surely; this is NOT `thm-busemann`. -/
theorem iidCodes_ae_boundaryBusemannLDP_of_P1
    (hP1 : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, CutWindowP1Family ω) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannLDP
              (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) ∧
          (∀ l k : ℤ, 0 ≤ l → l < k →
            ∀ hr : Reachable
              (boundaryPresentVertex (fun i => ω (i + 1)) h l)
              (boundaryPresentVertex (fun i => ω (i + 1)) h k),
              (presentLdpFiniteNat
                (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin) hr : ℤ) ≤
                X l - X k) ∧
          (∀ k : ℤ, 1 ≤ k → X k - X (k - 1) ≤ -1) := by
  have hAvoid := ae_cutWindow_finiteAvoidance_of_P1 hP1
  filter_upwards [hP1, hAvoid,
    iidCodes_ae_boundaryBusemannLDP_of_windowFiniteAvoidance]
    with ω _ hωAvoid hωBusemann
  obtain ⟨hfin, hωBusemann⟩ := hωBusemann
  obtain ⟨h, hBusemann⟩ := hωBusemann
  obtain ⟨X, hX, hUnique, hTriangle, hIncrement⟩ := hBusemann (hωAvoid h)
  exact ⟨hfin, h, X, hX, hUnique, hTriangle, hIncrement⟩

end DirectedDistances.KMSW
