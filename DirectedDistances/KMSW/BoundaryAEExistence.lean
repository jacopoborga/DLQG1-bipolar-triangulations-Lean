module

public import DirectedDistances.KMSW.BusemannFromCut
public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.BoundaryEnumeration
import DirectedDistances.KMSW.CommonFutureM0
import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.KMSW.LocalFinitenessIID

/-! # Almost-sure existence and combined boundary properties

Existence-first packaging for the iid boundary witnesses and the finite-stage
boundary properties proved in the neighboring KMSW modules. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open scoped Classical

/-- The iid hit-indexed boundary enumeration has an existing witness and the
the earlier universally quantified witness statement by making existence
explicit. -/
theorem iidCodes_ae_exists_boundaryCommonSequence :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        BusemannCommonSequenceHypothesis
          (fun k : ℤ => (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
            PresentVertex (fun i => ω (i + 1)))) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h
  exact ⟨h, boundaryEnumeration_commonSequence (fun i => ω (i + 1)) h⟩

/-- Almost surely the iid code has finite incidence, a hit-indexed lower
boundary enumeration, exactly the left-boundary sources, no allocated sinks,
and a common reachable sequence for its enumerated boundary vertices -/
theorem iidCodes_ae_boundaryProperties :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ _hfin : ∀ v : ℕ,
          {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∃ h : BoundaryHitWitnesses w,
          Function.Injective (boundaryVertex w h) ∧
          (kmswStage w 0).LR = [0] ∧
          (kmswStage w 0).west 0 = boundaryVertex w h 0 ∧
          (kmswStage w 0).east 0 = boundaryVertex w h 1 ∧
          (kmswStage w 0).present 0 = true ∧
          (∀ k : ℤ, 1 ≤ k →
            ∃ N, boundaryHitTime w h k ≤ N ∧
              ∀ n, N ≤ n →
                act w (boundaryHitTime w h k) ∈ (kmswStage w n).LR ∧
                (kmswStage w n).present (act w (boundaryHitTime w h k)) = true ∧
                (kmswStage w n).west (act w (boundaryHitTime w h k)) =
                  boundaryVertex w h k ∧
                (kmswStage w n).east (act w (boundaryHitTime w h k)) =
                  boundaryVertex w h (k + 1)) ∧
          (∀ k : ℤ, k ≤ -1 →
            let e := kmswLLCreatedEdge w (boundaryHitTime w h (k - 1));
            (kmswStage w (boundaryHitTime w h (k - 1))).west e =
              boundaryVertex w h (k - 1) ∧
            (kmswStage w (boundaryHitTime w h (k - 1))).east e =
              boundaryVertex w h k ∧
            (kmswStage w (boundaryHitTime w h (k - 1))).present e = false) ∧
          (∀ v : ℕ,
            (∃ n e, (e ∈ (kmswStage w n).LL ∨ e ∈ (kmswStage w n).LR) ∧
              ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)) →
            ∃ k : ℤ, boundaryVertex w h k = v) ∧
          (∀ v : ℕ,
            (∃ n, v < (kmswStage w n).nextVertex) →
              ((¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
                ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k)) ∧
          (∀ v : ℕ,
            (∃ n, v < (kmswStage w n).nextVertex) →
              ∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
          BusemannCommonSequenceHypothesis
            (fun k : ℤ => (⟨boundaryVertex w h k⟩ : PresentVertex w)) := by
  filter_upwards [iidCodes_ae_finite_incident_edges,
    iidCodes_ae_boundaryEnumeration, iidCodes_ae_sources,
    iidCodes_ae_no_sink, iidCodes_ae_exists_boundaryCommonSequence]
    with ω hfin henum hsources hsink hcommon
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  change ∃ hfin : ∀ v : ℕ,
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
    ∃ h : BoundaryHitWitnesses w, _
  refine ⟨?_, ?_⟩
  · intro v
    simpa only [w] using hfin v
  · obtain ⟨h, hinj, hLR, hwest, heast, hpresent, hright, hleft, hcover⟩ := henum
    obtain ⟨hs, hsource⟩ := hsources
    have hse : hs = h := Subsingleton.elim _ _
    obtain ⟨hc, hcommon⟩ := hcommon
    have hce : hc = h := Subsingleton.elim _ _
    subst hs
    subst hc
    refine ⟨h, hinj, hLR, hwest, heast, hpresent, hright, hleft, hcover,
      ?_, ?_, ?_⟩
    · intro v hv
      exact hsource v hv
    · intro v hv
      exact hsink v hv
    · exact hcommon

end DirectedDistances.KMSW
