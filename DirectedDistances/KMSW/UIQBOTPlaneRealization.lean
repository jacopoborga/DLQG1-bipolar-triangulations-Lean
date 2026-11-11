module

public import DirectedDistances.KMSW.UIQBOTGeneralCarrierVertices
public import DirectedDistances.KMSW.KMSWConstructedRealizationProof




public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PlanarMap

/-- Helper toward Definition 4.1: almost surely the constructed KMSW drawing
exists with the limit rotation, has a unique unbounded face, and its bordering
darts are exactly the limit external darts. -/
theorem uiqbot_ae_constructed_plane_realization :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∃ htrans : Tendsto (L w) atTop atTop,
          ∃ hR : ∀ a : ℤ, ∃ n, R w n ≤ a,
            ∃ hL0 : ∀ j, 0 ≤ L w j,
              KMSWConstructedPlaneRealizationStatement w hfin htrans hR hL0 := by
  filter_upwards [uiqbot_ae_general_source_sink_carrier] with ω hω
  let w := pitmanCode (fun i => ω (i + 1))
  rcases hω with ⟨hfin, htrans, hR, hL0, _⟩
  exact ⟨hfin, htrans, hR, hL0,
    kmswConstructedPlaneRealization w hfin htrans hR hL0⟩

end DirectedDistances.KMSW
