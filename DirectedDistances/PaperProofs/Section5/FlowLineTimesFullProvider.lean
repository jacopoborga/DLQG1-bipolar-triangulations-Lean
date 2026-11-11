module

public import DirectedDistances.PaperProofs.Section5.FlowLineTimesAnchorProvider
public import DirectedDistances.KMSW.MhatPrimeFaceSource

/- # Candidate packaging of flow-line clauses with a formal limiting-successor cycle

Candidate packaging of the local almost-sure clauses with a formal
limiting-successor cycle predicate. Identification with faces of the source map
Lemma 5.12. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Filter MeasureTheory
open DirectedDistances.KMSW
open DirectedDistances.RandomWalk

/- Candidate packaging of flow-line clauses and a formal limit-successor cycle; -/
theorem lemma_5_12_provider :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      ∃ hfin : ∀ v : ℕ,
        {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨
            (kmswStage w n).east e = v)}.Finite,
      ∃ hb : BoundaryHitWitnesses w,
      ∃ h : HasFlowLineHits w,
        FlowLineTimesJointMinima w h ∧
        FlowLineTimesItemI w h ∧
        FlowLineTimesItemII w hfin hb h ∧
        ∀ k, 1 ≤ k →
          let r := sourceFlowNR w h (k - 1)
          let t := sourceFlowNL w h (k - 1)
          let s := kmswStage w (t - 1)
          let e := if k = 1 then s.nextEdge + 1 else act w (r - 1)
          MhatPrimeTriangleFace w hfin
            ({act w (t - 1), act w t, e} : Multiset ℕ) := by
  filter_upwards [lemma_5_12_local_part] with ω hlocal
  change ∃ hfin : ∀ v : ℕ,
      {e : ℕ | ∃ n, e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
        ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
          (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
    ∃ hb : BoundaryHitWitnesses (fun i => ω (i + 1)),
    ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
      FlowLineTimesJointMinima (fun i => ω (i + 1)) h ∧
      FlowLineTimesItemI (fun i => ω (i + 1)) h ∧
      FlowLineTimesItemII (fun i => ω (i + 1)) hfin hb h ∧
      ∀ k, 1 ≤ k →
        let r := sourceFlowNR (fun i => ω (i + 1)) h (k - 1)
        let t := sourceFlowNL (fun i => ω (i + 1)) h (k - 1)
        let s := kmswStage (fun i => ω (i + 1)) (t - 1)
        let e :=
          if k = 1 then s.nextEdge + 1 else act (fun i => ω (i + 1)) (r - 1)
        MhatPrimeTriangleFace (fun i => ω (i + 1)) hfin
          ({act (fun i => ω (i + 1)) (t - 1),
            act (fun i => ω (i + 1)) t, e} : Multiset ℕ)
  obtain ⟨hfin, hb, h, hmin, hitemI, hitemII⟩ := hlocal
  exact ⟨hfin, hb, h, hmin, hitemI, hitemII,
    flowLineTimes_mhatPrimeFace (fun i => ω (i + 1)) hfin hb h⟩

end DirectedDistances.PaperProofs.Section5
