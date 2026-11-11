module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.KMSW.CommonFutureM0
public import DirectedDistances.KMSW.LocalFinitenessIID

/-! # `M_{0,∞}` Busemann characterization with only the window finite-avoidance premise

for the boundary enumeration `x_k = boundaryVertex w h k`, with the common-sequence
premise discharged by `boundaryEnumeration_commonSequence`
finite-avoidance statement, whose producer `lem-infty-cut` (cut vertices of
Hence this file does not prove `thm-busemann`. LDP is `-∞` and SDP is `+∞` on
unreachable pairs; only finite values on reachable pairs are used. -/

@[expose] public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory






theorem boundaryBusemannSDP_of_windowFiniteAvoidance (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (havoid : ∀ K : ℕ, ∃ z : PresentVertex w,
      ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
        FiniteAvoidance (⟨boundaryVertex w h k⟩ : PresentVertex w) z) :
    ∃ X : ℤ → ℤ, IsBoundaryBusemannSDP (boundaryPresentVertex w h) X ∧
      (∀ X' : ℤ → ℤ, IsBoundaryBusemannSDP (boundaryPresentVertex w h) X' → X' = X) ∧
      (∀ l k : ℤ, 0 ≤ l → l < k →
        X l - X k ≤
          ((sdp (boundaryPresentVertex w h l) (boundaryPresentVertex w h k)).toNat : ℤ)) ∧
      (∀ k : ℤ, 1 ≤ k → -1 ≤ X k - X (k - 1)) :=
  boundaryBusemannSDP_properties w h havoid (boundaryEnumeration_commonSequence w h)





theorem boundaryBusemannLDP_of_windowFiniteAvoidance (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w)
    (havoid : ∀ K : ℕ, ∃ z : PresentVertex w,
      ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
        FiniteAvoidance (⟨boundaryVertex w h k⟩ : PresentVertex w) z) :
    ∃ X : ℤ → ℤ,
      IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin)
        (boundaryPresentVertex w h) X ∧
      (∀ X' : ℤ → ℤ,
        IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin)
          (boundaryPresentVertex w h) X' → X' = X) ∧
      (∀ l k : ℤ, 0 ≤ l → l < k →
        ∀ hr : Reachable (boundaryPresentVertex w h l) (boundaryPresentVertex w h k),
          (presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin) hr : ℤ) ≤
            X l - X k) ∧
      (∀ k : ℤ, 1 ≤ k → X k - X (k - 1) ≤ -1) :=
  boundaryBusemannLDP_properties w hfin h havoid (boundaryEnumeration_commonSequence w h)

/-- Almost surely for iid codes, there exists a boundary-hit witness `h` (a.s. theorem
`iidCodes_ae_boundaryHitWitnesses`) such that window finite avoidance of the boundary
enumeration implies the SDP conclusions of
`boundaryBusemannSDP_of_windowFiniteAvoidance`. The window premise is not
proved here (producer `lem-infty-cut`); this is not `thm-busemann`. -/
theorem iidCodes_ae_boundaryBusemannSDP_of_windowFiniteAvoidance :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        (∀ K : ℕ, ∃ z : PresentVertex (fun i => ω (i + 1)),
          ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
            FiniteAvoidance
              (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
                PresentVertex (fun i => ω (i + 1))) z) →
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) h) X' →
              X' = X) ∧
          (∀ l k : ℤ, 0 ≤ l → l < k →
            X l - X k ≤
              ((sdp (boundaryPresentVertex (fun i => ω (i + 1)) h l)
                (boundaryPresentVertex (fun i => ω (i + 1)) h k)).toNat : ℤ)) ∧
          (∀ k : ℤ, 1 ≤ k → -1 ≤ X k - X (k - 1)) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω hωh
  exact ⟨hωh, fun havoid => boundaryBusemannSDP_of_windowFiniteAvoidance _ hωh havoid⟩

/-- Almost surely for iid codes, local finiteness holds (a.s. theorem
`iidCodes_ae_finite_incident_edges`) and there exists a boundary-hit witness (a.s.
theorem `iidCodes_ae_boundaryHitWitnesses`) for which window finite avoidance of the boundary enumeration implies the LDP conclusions of
`boundaryBusemannLDP_of_windowFiniteAvoidance`. The window premise is not proved
here (producer `lem-infty-cut`); this is not `thm-busemann`. -/
theorem iidCodes_ae_boundaryBusemannLDP_of_windowFiniteAvoidance :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        (∀ K : ℕ, ∃ z : PresentVertex (fun i => ω (i + 1)),
          ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
            FiniteAvoidance
              (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
                PresentVertex (fun i => ω (i + 1))) z) →
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannLDP
              (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) ∧
          (∀ l k : ℤ, 0 ≤ l → l < k →
            ∀ hr : Reachable (boundaryPresentVertex (fun i => ω (i + 1)) h l)
                (boundaryPresentVertex (fun i => ω (i + 1)) h k),
              (presentLdpFiniteNat
                (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin) hr : ℤ) ≤
                X l - X k) ∧
          (∀ k : ℤ, 1 ≤ k → X k - X (k - 1) ≤ -1) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses, iidCodes_ae_finite_incident_edges]
    with ω hωh hωfin
  exact ⟨hωfin, hωh, fun havoid =>
    boundaryBusemannLDP_of_windowFiniteAvoidance _ hωfin hωh havoid⟩

end DirectedDistances.KMSW
