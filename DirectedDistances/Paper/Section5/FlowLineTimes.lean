 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.FlowLineTimesFace

/-!
# Lemma 5.12 (`lem-flow-line-times`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/














public section
namespace DirectedDistances.Paper.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open scoped Topology

 
theorem flow_line_times :
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
                  ∀ d ∈ ds, Q.dartBorders d G.val :=
 
by exact DirectedDistances.PaperProofs.SourceResults.flow_line_times_face
 
 

end DirectedDistances.Paper.Section5
 
