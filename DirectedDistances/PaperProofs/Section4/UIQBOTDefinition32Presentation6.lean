module

public import DirectedDistances.PaperProofs.Section4.UIQBOTDefinition32Presentation5
public import DirectedDistances.PlanarMap.PLDrawingWindingSides17
public import DirectedDistances.PlanarMap.PLDrawingWindingSides10

/-! # UIQBOT repeated boundary side incidences -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open Filter unitInterval

/-- Helper toward Definition 3.2: the bordering-face winding-side test
holds at parameters strictly inside a segment or at a non-collinear bend. -/
theorem dartBorders_toPath_leftAtOn_of_strictSegment_or_nonzeroTurn
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams}) :
    (∃ i, i + 1 < (P.arc d).points.length ∧
      Polyline.segmentParameterStart i < (s.1 : ℝ) ∧
      (s.1 : ℝ) < Polyline.segmentParameterEnd (P.arc d).points.length i) ∨
    (∃ i, i + 2 < (P.arc d).points.length ∧
      (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1) ∧
      (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
        ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im ≠ 0) →
    LeftAtOn F.val (P.arc d).toPath s := by
  intro h
  rcases h with ⟨i, hi, hstart, hend⟩ | ⟨i, hi, hbend, hturn⟩
  · exact P.dartBorders_toPath_leftAtOn_of_strictSegment
      hvert d F hborder s hi hstart hend
  · exact P.dartBorders_toPath_leftAtOn_of_bend_turn_ne_zero
      hvert d F hborder s hi hbend hturn

















































end DirectedDistances.PaperProofs.Section4

end
