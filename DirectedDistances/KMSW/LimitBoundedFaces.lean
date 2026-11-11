module

public import DirectedDistances.KMSW.MonotoneLimitFaces
public import DirectedDistances.KMSW.MonotoneExteriorPaths
public import DirectedDistances.KMSW.TwoSidedDrawingFaceClassification
public import DirectedDistances.PaperProofs.Section4.GeoExistPlanar

/-! Helper toward Definition 3.8 / Theorem 1.4 (plane realization: bounded faces of the
monotone-family drawing); not a paper result. The source definition is

`monotoneLimit_dartBorders_iff` has the following full conclusion, under its
displayed hypotheses in `MonotoneLimitFaces.lean`:

```lean
exists U : P.Face,
  U.val = monotoneLimitExteriorRegion w Q G /\
  P.IsUnbounded U /\
  (forall F : P.Face, P.IsUnbounded F -> F = U) /\
  (forall F : P.Face,
    F = U \/ exists n i, F.val = ((G n).cap i).region) /\
  forall d, P.dartBorders d U <-> limitExternalDart w d
```

The one-sided and two-sided drawing-classification theorems retain only
`P.IsUnbounded U`, uniqueness, and the last dart-border clause. They discard
the exterior-set identity and, crucially, the face partition in the fourth
conjunct.

The cap is `(G n).cap i : GraphCap`, inherited from
`MonotoneStageCertificate.cap`. The exact declarations defining it are:

```lean
structure GraphCap where
  a b : ℝ
  low high : ℝ → ℝ
  ab : a < b
  low_continuous : ContinuousOn low (Icc a b)
  high_continuous : ContinuousOn high (Icc a b)
  separated : ∀ x ∈ Ioo a b, low x < high x
  left_join : low a = high a
  right_join : low b = high b

def GraphCap.region (C : GraphCap) : Set ℂ :=
  graphRegion C.a C.b C.low C.high
```

The certificate fields are exactly
`cap : Fin (kmswStage w n).triangles.length → GraphCap`,
`cap_avoid : ∀ i, Disjoint (cap i).region P.image`, and
`cover : P.image ∪ ⋃ i, closure (cap i).region =
closedGraphRegion xmin xmax lower upper`.
The exact limit coverage premise of `monotoneLimit_dartBorders_iff` is
`hcover : ∀ z, z ∉ P.image → z ∉ monotoneLimitExteriorRegion w Q G →
∃ n i, z ∈ ((G n).cap i).region`. The family wrapper uses
`hcover : ∀ z, (∀ n, z ∉ (familyQ w hfam n).image) →
z ∉ monotoneLimitExteriorRegion w (familyQ w hfam) (familyG w hfam) →
∃ n i, z ∈ ((familyG w hfam n).cap i).region`.

`MonotoneLimitCapPersistence w Q G` is exactly
`∀ n i m, n ≤ m → ∃ j,
  ((G n).cap i).region = ((G m).cap j).region`.
The family lemma `family_cap_persistence` supplies it. The private
`cap_avoids_limitImage` lemma has conclusion
`Disjoint ((G n).cap i).region P.image`, assuming exactly `hfin`,
`hpos : ∀ n v, P.pos v.val = (Q n).pos v`,
`harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d`, cap persistence, `n`,
and `i`, where
`hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite` and
`P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
  (kmswInfRot w hfin) (kmswLimitDartVertex w)`.
The public `monotoneLimit_cap_faces` conclusion is exactly
`∀ n i, ∃ F : P.Face,
  F.val = ((G n).cap i).region ∧ Bornology.IsBounded F.val`.
That proof uses private avoidance: an alleged intersection moves to stage
`max n m`, contradicting that stage cap's `cap_avoid`. Thus cap regions are
image-free; coverage and connected-component identification give the bounded
face classification.

The file proves that classification from exactly the hypotheses of each
existing one-sided or two-sided classification theorem. It does not identify
the cap's bordering darts with an orbit of `kmswInfFaceSucc`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization: bounded faces of the
The one-sided classification hypotheses imply that every bounded face of the
monotone-family drawing is exactly a persistent stage-cap region. -/
theorem limitDrawing_boundedFace_eq_capRegion (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hF : ¬ (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded F) :
    ∃ n i, F.val =
      ((familyG w (monotone_family_all w) n).cap i).region := by
  let hfam := monotone_family_all w
  let Q : ∀ n, StageDrawing w n := familyQ w hfam
  let G : ∀ n, MonotoneStageInvariant w n (Q n) := familyG w hfam
  let P := monotoneFamilyDrawing w hfin hfam
  have hbd : monotoneRegionBoundedExhaustion Q G :=
    monotoneRegionBoundedExhaustion_of_KMSW w hfin htrans hR hL0 Q G
  have hpos : ∀ n v, P.pos v.val = (Q n).pos v := familyDrawing_pos w hfin hfam
  have harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d :=
    familyDrawing_arc w hfin hfam
  have hpersist : MonotoneLimitCapPersistence w Q G :=
    family_cap_persistence w hfam
  have himage : P.image = ⋃ n, (Q n).image := monotoneFamilyDrawing_image w hfin hfam
  have hfront : frontier (monotoneLimitExteriorRegion w Q G) ⊆ P.image := by
    rw [himage]
    exact monotoneLimitExterior_frontier_subset_trace Q G hbd
  have hdisj : Disjoint (monotoneLimitExteriorRegion w Q G) P.image := by
    rw [himage]
    apply disjoint_left.mpr
    intro z hzE hzImage
    obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hzImage
    exact (disjoint_left.mp (monotoneLimitExterior_disjoint_stageImage Q G n))
      hzE hzn
  have hcover : ∀ z ∉ P.image,
      z ∉ monotoneLimitExteriorRegion w Q G →
        ∃ n i, z ∈ ((G n).cap i).region := by
    intro z hzImage hzE
    apply monotoneStageRegionUnion_mem_cap_of_not_trace Q G (not_not.mp hzE)
    simp only [monotoneLayoutTraceUnion, Set.mem_iUnion, not_exists]
    intro n hzn
    apply hzImage
    rw [himage]
    exact Set.mem_iUnion.mpr ⟨n, hzn⟩
  have hEopen := monotoneLimitExterior_isOpen_of_boundedExhaustion Q G hbd
  have hEconn := monotoneLimitExterior_isPathConnected_of_KMSW
    w hfin htrans hR hL0 Q G
  have hEunb : ∀ R : ℝ, ∃ z ∈ monotoneLimitExteriorRegion w Q G, R < ‖z‖ := by
    intro R
    exact monotoneLimitExterior_unbounded_of_xmin_zero Q G
      (fun n => monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 (G n)) R
  obtain ⟨U, _, hU, _, hpartition⟩ := monotoneLimit_faces_partition w hfin Q G P
    hpos harc hpersist hEopen hEconn hEunb hfront hdisj hcover
  have hF' : F = U ∨ ∃ n i, F.val = ((G n).cap i).region := hpartition F
  rcases hF' with hFU | ⟨n, i, hFi⟩
  · subst F
    exact (hF hU).elim
  · exact ⟨n, i, hFi⟩

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization: bounded faces of the
The two-sided classification hypotheses imply the same persistent-cap
classification of bounded faces. -/
theorem limitDrawing_boundedFace_eq_capRegion_twoSided (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hF : ¬ (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded F) :
    ∃ n i, F.val =
      ((familyG w (monotone_family_all w) n).cap i).region := by
  let hfam := monotone_family_all w
  let Q : ∀ n, StageDrawing w n := familyQ w hfam
  let G : ∀ n, MonotoneStageInvariant w n (Q n) := familyG w hfam
  let P := monotoneFamilyDrawing w hfin hfam
  have hbd : monotoneRegionBoundedExhaustion Q G :=
    monotoneRegionBoundedExhaustion_twoSided w hfin h Q G
  have hpos : ∀ n v, P.pos v.val = (Q n).pos v := familyDrawing_pos w hfin hfam
  have harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d :=
    familyDrawing_arc w hfin hfam
  have hpersist : MonotoneLimitCapPersistence w Q G :=
    family_cap_persistence w hfam
  have himage : P.image = ⋃ n, (Q n).image := monotoneFamilyDrawing_image w hfin hfam
  have hfront : frontier (monotoneLimitExteriorRegion w Q G) ⊆ P.image := by
    rw [himage]
    exact monotoneLimitExterior_frontier_subset_trace Q G hbd
  have hdisj : Disjoint (monotoneLimitExteriorRegion w Q G) P.image := by
    rw [himage]
    apply disjoint_left.mpr
    intro z hzE hzImage
    obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hzImage
    exact (disjoint_left.mp (monotoneLimitExterior_disjoint_stageImage Q G n))
      hzE hzn
  have hcover : ∀ z ∉ P.image,
      z ∉ monotoneLimitExteriorRegion w Q G →
        ∃ n i, z ∈ ((G n).cap i).region := by
    intro z hzImage hzE
    apply monotoneStageRegionUnion_mem_cap_of_not_trace Q G (not_not.mp hzE)
    simp only [monotoneLayoutTraceUnion, Set.mem_iUnion, not_exists]
    intro n hzn
    apply hzImage
    rw [himage]
    exact Set.mem_iUnion.mpr ⟨n, hzn⟩
  have hEopen := monotoneLimitExterior_isOpen_of_boundedExhaustion Q G hbd
  have hEconn := monotoneLimitExterior_isPathConnected_twoSided w hfin h Q G
  have hEunb : ∀ R : ℝ, ∃ z ∈ monotoneLimitExteriorRegion w Q G, R < ‖z‖ := by
    intro R
    exact monotoneLimitExterior_unbounded_twoSided Q G R
  obtain ⟨U, _, hU, _, hpartition⟩ := monotoneLimit_faces_partition w hfin Q G P
    hpos harc hpersist hEopen hEconn hEunb hfront hdisj hcover
  have hF' : F = U ∨ ∃ n i, F.val = ((G n).cap i).region := hpartition F
  rcases hF' with hFU | ⟨n, i, hFi⟩
  · subst F
    exact (hF hU).elim
  · exact ⟨n, i, hFi⟩

end DirectedDistances.KMSW
