module

public import DirectedDistances.PaperProofs.Section4.ThinCutCompatibility
public import DirectedDistances.PlanarMap.PlanarPathCutAncestorReroute
















public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open scoped Classical

private theorem side_cutL_endpoints {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutLRep R hR).2.dartCount) :
    cutLRepVertexMap R hR (dartTailVertex (cutLRep R hR).2.B.map d) =
        dartTailVertex R.B.map (cutLRepDartMap R hR d) ∧
      cutLRepVertexMap R hR (dartHeadVertex (cutLRep R hR).2.B.map d) =
        dartHeadVertex R.B.map (cutLRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  constructor
  · exact (congrArg (pathCutLeftHalfVertexMap R.B P)
      (I.vertexEquiv_dartTailVertex d)).trans
        (pathCutLeftHalfVertexMap_dartTailVertex R.B P (I.toEquiv d))
  · exact (congrArg (pathCutLeftHalfVertexMap R.B P)
      (I.vertexEquiv_dartHeadVertex d)).trans
        (pathCutLeftHalfVertexMap_dartHeadVertex R.B P (I.toEquiv d))

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
Within the original finite base, the image of the left half selected darts is exactly the
set of ambient selected darts of the image target lying in the range of the half dart map. -/
theorem cutLRep_selectedDarts_image_iff {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (v : MapVertex (cutLRep R hR).2.B.map) (e : Fin R.dartCount) :
    e ∈ cutLRepDartMap R hR '' selectedDarts (presentation (cutLRep R hR).2 .left v) ↔
      e ∈ Set.range (cutLRepDartMap R hR) ∧
        e ∈ selectedDarts (presentation R .left (cutLRepVertexMap R hR v)) := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, rfl⟩, cutLRep_selectedDarts_map R hR v d hd⟩
  · rintro ⟨⟨d, rfl⟩, h⟩
    refine ⟨d, ⟨?_, ?_⟩, rfl⟩
    · refine (cutLRep_ancestors_map_iff R hR _ v).mpr ?_
      rw [(side_cutL_endpoints R hR d).1]
      exact h.1
    · refine (cutLRep_ancestors_map_iff R hR _ v).mpr ?_
      rw [(side_cutL_endpoints R hR d).2]
      exact h.2

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
Prefix agreement of the selected geodesics of two cut representatives, as dart and vertex
images in a common target: the first representative has length `m ≤ m'` and its `m` selected
darts (and `m + 1` vertices) have the same images as the first ones of the second
representative. -/
@[expose] def CommonSelectedPrefix {x : XDP} {ℓ r n m ℓ' r' n' m' : ℕ} {α β : Type*}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (fd : Fin R.dartCount → α) (gd : Fin S.dartCount → α)
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β) : Prop :=
  m ≤ m' ∧
    (∀ i < m, ∃ (e : Fin R.dartCount) (e' : Fin S.dartCount),
      (selectedGeodesicOfLen R.B x hR).darts[i]? = some e ∧
        (selectedGeodesicOfLen S.B x hS).darts[i]? = some e' ∧ fd e = gd e') ∧
    (∀ i ≤ m, ∃ (u : MapVertex R.B.map) (u' : MapVertex S.B.map),
      (selectedGeodesicOfLen R.B x hR).vertices[i]? = some u ∧
        (selectedGeodesicOfLen S.B x hS).vertices[i]? = some u' ∧ fv u = gv u')

private theorem side_seam_image_iff {δ ε α : Type*} (P : ℕ → δ → Prop) (mp : δ → ε)
    (F : ε → α) (G : List ε) (c : ℕ)
    (h : ∀ (i : ℕ) (e : ε), (∃ d, P i d ∧ mp d = e) ↔ i < c ∧ G[i]? = some e)
    (i : ℕ) (z : α) :
    (∃ d, P i d ∧ F (mp d) = z) ↔ i < c ∧ ∃ e, G[i]? = some e ∧ F e = z := by
  constructor
  · rintro ⟨d, hd, hz⟩
    obtain ⟨hi, he⟩ := (h i (mp d)).mp ⟨d, hd, rfl⟩
    exact ⟨hi, _, he, hz⟩
  · rintro ⟨hi, e, he, hz⟩
    obtain ⟨d, hd, rfl⟩ := (h i e).mpr ⟨hi, he⟩
    exact ⟨d, hd, hz⟩

/-- Helper toward Proposition 4.7 (prop-thin-decoder); not a paper result.
Under `CommonSelectedPrefix`, the surviving left-half seam marks of the shorter cut `R`,
read in the common target, are an initial segment of the images of the selected geodesic of
the longer cut `S`. -/
theorem cutLRep_seam_marks_common_prefix {x : XDP} {ℓ r n m ℓ' r' n' m' : ℕ} {α β : Type*}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (fd : Fin R.dartCount → α) (gd : Fin S.dartCount → α)
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS fd gd fv gv) (s : ℕ)
    (v : MapVertex (cutLRep R hR).2.B.map) (hs : s + 1 ≤ ℓ)
    (hv : boundaryTarget (cutLRep R hR).2.B .left s = some v) :
    ∃ c < m, ∀ (i : ℕ) (z : α),
      (∃ d : selectedDarts (presentation (cutLRep R hR).2 .left v),
        (boundaryDarts (cutLRep R hR).2.B .right)[i]? = some d.1 ∧
          fd (cutLRepDartMap R hR d.1) = z) ↔
      i < c ∧ ∃ e' : Fin S.dartCount,
        (selectedGeodesicOfLen S.B x hS).darts[i]? = some e' ∧ gd e' = z := by
  obtain ⟨c, hcm, hc⟩ := cutLRep_selected_seam_image R hR s v hs hv
  refine ⟨c, hcm, fun i z => ?_⟩
  refine (side_seam_image_iff
    (fun i (d : selectedDarts (presentation (cutLRep R hR).2 .left v)) =>
      (boundaryDarts (cutLRep R hR).2.B .right)[i]? = some d.1)
    (fun d => cutLRepDartMap R hR d.1) fd _ c hc i z).trans ?_
  refine and_congr_right fun hi => ?_
  obtain ⟨e, e', he, he', hf⟩ := hP.2.1 i (lt_trans hi hcm)
  constructor
  · rintro ⟨e1, h1, hz⟩
    have : e1 = e := Option.some.inj (h1.symm.trans he)
    subst this
    exact ⟨e', he', hf ▸ hz⟩
  · rintro ⟨e1, h1, hz⟩
    have : e1 = e' := Option.some.inj (h1.symm.trans he')
    subst this
    exact ⟨e, he, hf.trans hz⟩

end DirectedDistances.PaperProofs.Section4
