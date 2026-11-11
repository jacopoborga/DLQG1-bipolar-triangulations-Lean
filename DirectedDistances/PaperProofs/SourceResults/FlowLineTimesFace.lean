module

public import DirectedDistances.PaperProofs.Section5.FlowTrianglePrimePlaneFace

/-! Isolated proof provider for Lemma 5.12 (lem-flow-line-times); packaging only. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open scoped Topology

/-- Lemma 5.12 isolated provider (lem-flow-line-times, -/
theorem flow_line_times_face :
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
          let e :=
            if k = 1 then (kmswStage w (t - 1)).nextEdge + 1
            else act w (r - 1)
          let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
          ∃ j : TriangleCreationTime w,
            j.val = t - 1 ∧
            j.val + 1 = t ∧
            stageTriangleRecord w j = (act w (t - 1), act w t, e) ∧
            ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
              (kmswStage w (j.val + 1)).triangles.get i =
                stageTriangleRecord w j ∧
              ∃ G : MhatPrimeFaces w hfin hb (monotone_family_all w),
                G.val.val =
                  ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
                ∃ ds :
                    List (RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb)),
                  ds.length = 3 ∧
                  (↑(ds.map (fun d =>
                    (restrictedDartEquivPrimeDart w hfin hb d).1.val)) :
                    Multiset ℕ) =
                    {act w (t - 1), act w t, e} ∧
                  frontier G.val.val = ⋃ d ∈ ds, (Q.arc d).image ∧
                  ∀ d ∈ ds, Q.dartBorders d G.val := by
  filter_upwards [DirectedDistances.PaperProofs.Section5.lemma_5_12_provider]
    with ω hprovider
  obtain ⟨hfin, hb, h, hmin, hitemI, hitemII, _⟩ := hprovider
  exact ⟨hfin, hb, h, hmin, hitemI, hitemII,
    flowTriangle_prime_plane_face (fun i => ω (i + 1)) hfin hb h⟩

end DirectedDistances.PaperProofs.SourceResults
