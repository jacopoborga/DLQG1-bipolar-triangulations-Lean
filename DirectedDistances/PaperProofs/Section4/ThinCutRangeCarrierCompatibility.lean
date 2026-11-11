module

public import DirectedDistances.PaperProofs.Section4.ThinCutSideCarrierCompatibility
public import DirectedDistances.PlanarMap.PlanarPathCutAncestorRerouteRight

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

The right selected-dart image is characterized by ambient ancestry and the
right-half dart range. Both dart-map ranges are identified with the respective -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open scoped Classical

private theorem range_cutR_endpoints {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutRRep R hR).2.dartCount) :
    cutRRepVertexMap R hR (dartTailVertex (cutRRep R hR).2.B.map d) =
        dartTailVertex R.B.map (cutRRepDartMap R hR d) ∧
      cutRRepVertexMap R hR (dartHeadVertex (cutRRep R hR).2.B.map d) =
        dartHeadVertex R.B.map (cutRRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  constructor
  · exact (congrArg (pathCutRightHalfVertexMap R.B P)
      (I.vertexEquiv_dartTailVertex d)).trans
        (pathCutRightHalfVertexMap_dartTailVertex R.B P (I.toEquiv d))
  · exact (congrArg (pathCutRightHalfVertexMap R.B P)
      (I.vertexEquiv_dartHeadVertex d)).trans
        (pathCutRightHalfVertexMap_dartHeadVertex R.B P (I.toEquiv d))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Within the original finite base, the image of the right half selected darts is exactly the
set of ambient selected darts of the image target lying in the range of the half dart map. -/
theorem cutRRep_selectedDarts_image_iff {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (v : MapVertex (cutRRep R hR).2.B.map) (e : Fin R.dartCount) :
    e ∈ cutRRepDartMap R hR '' selectedDarts (presentation (cutRRep R hR).2 .right v) ↔
      e ∈ Set.range (cutRRepDartMap R hR) ∧
        e ∈ selectedDarts (presentation R .right (cutRRepVertexMap R hR v)) := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, rfl⟩, cutRRep_selectedDarts_map R hR v d hd⟩
  · rintro ⟨⟨d, rfl⟩, h⟩
    refine ⟨d, ⟨?_, ?_⟩, rfl⟩
    · refine (cutRRep_ancestors_map_iff R hR _ v).mpr ?_
      rw [(range_cutR_endpoints R hR d).1]
      exact h.1
    · refine (cutRRep_ancestors_map_iff R hR _ v).mpr ?_
      rw [(range_cutR_endpoints R hR d).2]
      exact h.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The left dart-map range is exactly the closed left face/edge-flip carrier. -/
theorem cutLRepDartMap_range {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    Set.range (cutLRepDartMap R hR) =
      pathCutLeftHalfDarts R.B (selectedGeodesicOfLen R.B x hR) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  ext e
  constructor
  · rintro ⟨d, rfl⟩
    exact (I.toEquiv d).2
  · intro he
    let d : {e // e ∈ pathCutLeftHalfDarts R.B P} := ⟨e, he⟩
    refine ⟨I.toEquiv.symm d, ?_⟩
    change (I.toEquiv (I.toEquiv.symm d)).1 = e
    rw [Equiv.apply_symm_apply]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The right dart-map range is exactly the closed right face/edge-flip carrier. -/
theorem cutRRepDartMap_range {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m) :
    Set.range (cutRRepDartMap R hR) =
      pathCutRightHalfDarts R.B (selectedGeodesicOfLen R.B x hR) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  ext e
  constructor
  · rintro ⟨d, rfl⟩
    exact (I.toEquiv d).2
  · intro he
    let d : {e // e ∈ pathCutRightHalfDarts R.B P} := ⟨e, he⟩
    refine ⟨I.toEquiv.symm d, ?_⟩
    change (I.toEquiv (I.toEquiv.symm d)).1 = e
    rw [Equiv.apply_symm_apply]



















































end DirectedDistances.PaperProofs.Section4
