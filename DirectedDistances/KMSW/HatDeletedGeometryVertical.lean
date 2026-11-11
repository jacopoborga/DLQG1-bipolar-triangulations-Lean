module

public import DirectedDistances.KMSW.HatDeletedVertexEscape
import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsFull
import DirectedDistances.KMSW.HatBoundaryFacts
import DirectedDistances.KMSW.WindowModelHatCodes
import DirectedDistances.KMSW.RPhaseLawTransfer

/-! Helpers toward Lemma 5.13 (`lem-quad-kmsw`), not the paper result.

The existing finite-path escape construction supplies the full deleted-point
path obligation without a global vertical separation assumption. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward Lemma 5.13: every deleted ambient point joins every ambient
unbounded face in the reachable drawing's complement. The vertex escape and
deleted-arc reductions supply all paths, with no extra geometric premise. -/
theorem hatDeletedGeometryPathToAmbientExteriorGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedGeometryPathToAmbientExteriorGoal w hfin :=
  hatDeletedVertexPathToAmbientExteriorGoal_implies_deletedGeometryPath w hfin
    (hatDeletedVertexPathToAmbientExteriorGoal_holds w h hfin)

/-- Helper toward Lemma 5.13: the path construction supplies the root-face -/
theorem hatDeletedGeometryRootFaceConnectivityGoal_of_flowLineHits (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatDeletedGeometryRootFaceConnectivityGoal w h hfin :=
  hatDeletedGeometryPathToAmbientExteriorGoal_implies_rootFaceConnectivity w h hfin
    (hatDeletedGeometryPathToAmbientExteriorGoal_holds w h hfin)

/-- Helper toward Lemma 5.13: every bounded restricted face excludes the ambient -/
theorem hatBoundedFaceDeletedGeometryExclusionGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatBoundedFaceDeletedGeometryExclusionGoal w hfin :=
  hatDeletedGeometryRootFaceConnectivityGoal_implies_deletedGeometryExclusion w h hfin
    (hatDeletedGeometryRootFaceConnectivityGoal_of_flowLineHits w h hfin)

/-- Helper toward Lemma 5.13: every bounded restricted face borders a finite -/
theorem hatBoundedFaceFiniteBorderGoal_of_flowLineHits (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    hatBoundedFaceFiniteBorderGoal w h hfin :=
  hatDeletedGeometryPathToAmbientExteriorGoal_implies_boundedFaceFiniteBorder w h hfin
    (hatDeletedGeometryPathToAmbientExteriorGoal_holds w h hfin)

/-- Helper toward Lemma 5.13: the unbounded restricted face containing the
ambient exterior is unique. A different component avoids deleted geometry and
would therefore lie in an ambient face, which is either bounded or the same -/
theorem hatRealizedFaces_unbounded_unique (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    let Q := hatRealizedDrawing w hfin
    ∃ U : Q.Face, Q.IsUnbounded U ∧
      (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
      Q.dartBorders (hatLimitDartEquiv w h futureMapOuterDart) U := by
  classical
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  obtain ⟨E, U, hE, hEU, hU, hroot⟩ := hatRealizedFaces_unbounded_root_face w h hfin
  refine ⟨U, hU, ?_, hroot⟩
  intro F hF
  by_cases hdel : ∃ z ∈ F.val, z ∈ P.image
  · obtain ⟨z, hzF, hzP⟩ := hdel
    have hzQ := Q.face_subset_compl F hzF
    have hzU := hatDeletedGeometryRootFaceConnectivityGoal_of_flowLineHits
      w h hfin E U hE hEU hU hroot z hzP hzQ
    exact Q.faces_eq_of_mem hzF hzU
  · have havoid : F.val ⊆ P.imageᶜ := by
      intro z hz hzP
      exact hdel ⟨z, hz, hzP⟩
    obtain ⟨z, hzQ, hFset⟩ := F.property
    have hzF : z ∈ F.val := hFset ▸ mem_connectedComponentIn hzQ
    have hzP : z ∉ P.image := havoid hzF
    let A : P.Face := ⟨connectedComponentIn P.imageᶜ z, z, hzP, rfl⟩
    have hFA : F.val ⊆ A.val := by
      have hconn : IsPreconnected F.val := by
        rw [hFset]
        exact isPreconnected_connectedComponentIn
      exact hconn.subset_connectedComponentIn hzF havoid
    have hA : P.IsUnbounded A := by
      intro R
      obtain ⟨a, ha, hRa⟩ := hF R
      exact ⟨a, hFA ha, hRa⟩
    obtain ⟨E', _, huniq, _⟩ := monotoneFamilyDrawing_faceClassification_twoSided
      w hfin (hatBoundaryHitWitnesses w h)
    have hAE : A = E := (huniq A hA).trans (huniq E hE).symm
    have hzE : z ∈ E.val := hAE ▸ hFA hzF
    exact Q.faces_eq_of_mem hzF (hEU hzE)

/-- Helper toward Lemma 5.13: a fixed oriented dart borders at most one face. -/
private theorem face_eq_of_common_border {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F G : P.Face) (d : D) (hF : P.dartBorders d F) (hG : P.dartBorders d G) :
    F = G := by
  obtain ⟨a, ha, hF⟩ := hF
  obtain ⟨b, hb, hG⟩ := hG
  let t := min a b / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t < a := by
    have := min_le_left a b
    dsimp [t]
    linarith
  have htb : t < b := by
    have := min_le_right a b
    dsimp [t]
    linarith
  exact P.faces_eq_of_mem (hF t t ht hta ht hta) (hG t t ht htb ht htb)

/-- Helper toward Lemma 5.13: the endpoint test in the oriented triangle
definition distinguishes left and up creations. -/
private theorem creation_east_eq_iff (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    edgeEast w (stageTriangleRecord w j).1 =
      edgeEast w (stageTriangleRecord w j).2.1 ↔ w j.val = 0 := by
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  have hb := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
  rw [← (edge_endpoints_eq w hb.1).2, ← (edge_endpoints_eq w hb.2.1).2]
  have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
  have hne := ne_of_lt ha
  have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by
    omega
  have hv := (kmswStage_endpoints_lt_nextVertex w j.val _ ha).2
  rcases j.property with h0 | h1
  · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, h0, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, hp, State.addEdge, hne, hne']
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, h1, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge, hne, hne', ne_of_lt hv]

/-- Helper toward Lemma 5.13: the creation list and oriented triangle word -/
private theorem creation_oriented_mem (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (d : ℕ × Bool) :
    d ∈ triangleOrientedDarts w (stageTriangleRecord w j) ↔
      d ∈ stageTriangleDartList w j := by
  have he := creation_east_eq_iff w j
  rcases j.property with h0 | h1
  · have hh := he.mpr h0
    unfold triangleOrientedDarts
    rw [ite_eq_left hh]
    cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp only [stageTriangleDartList, stageTriangleDartTriple,
        stageTriangleRecord, h0, ↓reduceIte, hp,
        List.mem_cons, List.not_mem_nil, or_false]
    all_goals tauto
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    have hh := mt he.mp h0
    unfold triangleOrientedDarts
    rw [ite_eq_right hh]
    simp only [stageTriangleDartList, stageTriangleDartTriple,
      stageTriangleRecord, h0, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false]

/-- Helper toward Lemma 5.13: any dart bordering a bounded restricted face
belongs to a compressed triangle and is not persistently external. -/
private theorem bounded_border_not_external (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (G : PlaneFaces (hatRealizedDrawing w hfin)) (d : ℕ × Bool)
    (hd : (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) G.val) :
    ¬ limitExternalDart (hatCodes w h) d := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  let H := hatLimitDartEquiv w h
  let u := hatCodes w h
  obtain ⟨c, hcG, hcfinite⟩ := hatBoundedFaceFiniteBorderGoal_of_flowLineHits w h hfin G
  obtain ⟨j, k, i, F, G', _, _, hk, _, hi, hF, hG', hb⟩ :=
    hatFiniteFaceOrbit_realized w h hfin c hcfinite
  have hGG : G'.val = G.val := face_eq_of_common_border Q G'.val G.val (H c)
    (hb c (Equiv.Perm.SameCycle.refl _ _)) hcG
  have hFG : F.val.val = G.val.val :=
    hG'.symm.trans (congrArg Subtype.val hGG)
  have hdF : P.dartBorders (H d).val F.val := by
    exact dartBorders_transport Q P G.val F.val (H d) (H d).val hFG rfl hd
  let i' := (stageTriangleRecord_fin_index w k).choose
  have hi' := (stageTriangleRecord_fin_index w k).choose_spec
  have hcaps := monotone_cap_region_eq w
    (familyG w (monotone_family_all w) (k.val + 1))
    (familyG w (monotone_family_all w) (k.val + 1)) i i'
    (hi.trans hi'.symm) (fun _ _ => rfl)
  have hFcap : F.val = capFace w hfin k :=
    Subtype.ext (hF.trans (hcaps.trans (capFace_spec w hfin k).1.symm))
  have hmem : (H d).val ∈ triangleOrientedDarts w (stageTriangleRecord w k) := by
    apply (creation_oriented_mem w k _).mpr
    exact (cap_border_iff w hfin k _).mp (hFcap ▸ hdF)
  obtain ⟨i0, hi0⟩ := stageTriangleRecord_fin_index u j
  let t : HatLocalTri w h := ⟨stageTriangleRecord u j, j.val + 1,
    hi0 ▸ List.get_mem _ i0⟩
  have hmap := hatLimit_triangleOrientedDarts w h t
  change (triangleOrientedDarts u (stageTriangleRecord u j)).map
      (fun e => (H e).val) = triangleOrientedDarts w
        (hatLimitEdgeMap w h (stageTriangleRecord u j).1,
          hatLimitEdgeMap w h (stageTriangleRecord u j).2.1,
          hatLimitEdgeMap w h (stageTriangleRecord u j).2.2) at hmap
  rw [← hk] at hmap
  rw [← hmap] at hmem
  obtain ⟨e, he, hed⟩ := List.mem_map.mp hmem
  have hed' : e = d := H.injective (Subtype.ext hed)
  rw [hed'] at he
  exact stageTriangleDart_not_limitExternal u j d ((creation_oriented_mem u j d).mp he)

/-- Helper toward Lemma 5.13: every restricted dart borders a restricted
face, by enlarging an ambient face in the smaller drawing's complement. -/
private theorem restricted_dart_borders_exists (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) (d : ℕ × Bool) :
    ∃ F : (hatRealizedDrawing w hfin).Face,
      (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) F := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := hatRealizedDrawing w hfin
  let H := hatLimitDartEquiv w h
  have hsub : Q.image ⊆ P.image := restrictDrawing_image_subset P
    {d : ℕ × Bool | MhatGeometricEdge w d.1} (fun _ => Iff.rfl)
  obtain ⟨F, hdF⟩ := dart_borders_exists w hfin (hatBoundaryHitWitnesses w h) (H d).val
  obtain ⟨z, hz, hF⟩ := F.property
  have hzQ : z ∉ Q.image := fun hzQ => hz (hsub hzQ)
  let G : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
  have hFG : F.val ⊆ G.val := by
    rw [hF]
    exact connectedComponentIn_mono z (compl_subset_compl.mpr hsub)
  obtain ⟨δ, hδ, hw⟩ := hdF
  exact ⟨G, δ, hδ, fun t ε ht htδ hε hεδ => hFG (hw t ε ht htδ hε hεδ)⟩

/-- Helper toward Lemma 5.13: all persistently external compressed darts
border the unique unbounded restricted face. -/
theorem hatRealizedFaces_external_border_unbounded (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) :
    let Q := hatRealizedDrawing w hfin
    ∃ U : Q.Face, Q.IsUnbounded U ∧
      (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
      ∀ d, Q.dartBorders (hatLimitDartEquiv w h d) U ↔
        limitExternalDart (hatCodes w h) d := by
  classical
  let Q := hatRealizedDrawing w hfin
  obtain ⟨U, hU, huniq, _⟩ := hatRealizedFaces_unbounded_unique w h hfin
  refine ⟨U, hU, huniq, fun d => ⟨?_, ?_⟩⟩
  · exact hatRealizedFaces_unbounded_border_external w h hfin U hU d
  · intro hd
    obtain ⟨F, hdF⟩ := restricted_dart_borders_exists w h hfin d
    have hF : Q.IsUnbounded F := by
      by_contra hbounded
      change ¬ ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖ at hbounded
      push Not at hbounded
      obtain ⟨R, hR⟩ := hbounded
      have hFb : Bornology.IsBounded F.val := by
        apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
        exact ⟨R, fun z hz => by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hR z hz⟩
      exact bounded_border_not_external w h hfin ⟨F, hFb⟩ d hdF hd
    exact huniq F hF ▸ hdF

/-- Helper toward Lemma 5.13: the empty lower-left boundary forces the
compressed horizontal walk to be nonnegative. -/
private theorem hat_horizontal_nonneg (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (n : ℕ) : 0 ≤ L (hatCodes w h) n := by
  have hLL := kmswStage_LL_length (hatCodes w h) n
  rw [hat_LL_nil w h n] at hLL
  have hmin : minL (hatCodes w h) n = 0 := by
    simp only [List.length_nil, Nat.cast_zero] at hLL
    omega
  have hb := runningMin_le (L (hatCodes w h)) n n le_rfl
  change minL (hatCodes w h) n ≤ L (hatCodes w h) n at hb
  rw [hmin] at hb
  exact hb

/-- Helper toward Lemma 5.13: all external compressed darts are in the
face-successor orbit of the root's east dart. The only additional walk property
is compressed left transience; its almost-sure supply is proved below. -/
theorem hatExternalDart_iff_rootFaceCycle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop)
    (d : ℕ × Bool) :
    limitExternalDart (hatCodes w h) d ↔
      (kmswInfFaceSucc (hatCodes w h)
        (hatCodes_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d := by
  have horbit := limitExternalDart_iff_sameCycle (hatCodes w h)
    (hatCodes_finiteIncidence w h hfin) htrans
    (hat_R_unbounded_hatted w h) (hat_horizontal_nonneg w h)
  have hroot := (horbit futureMapOuterDart).mp (futureMapOuterDart_external _)
  exact ⟨fun hd => hroot.symm.trans ((horbit d).mp hd),
    fun hd => (horbit d).mpr (hroot.trans hd)⟩

/-- Helper toward Lemma 5.13: the exact unbounded-face identification goal,
including uniqueness, all external darts, and the full root orbit.
Compressed left transience is supplied almost surely by the code law, independently -/
theorem hatUnboundedFaceIdentificationGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop) :
    hatUnboundedFaceIdentificationGoal w h hfin := by
  obtain ⟨U, hU, huniq, hborder⟩ := hatRealizedFaces_external_border_unbounded w h hfin
  exact ⟨U, hU, huniq, hborder, hatExternalDart_iff_rootFaceCycle w h hfin htrans⟩

/-- Helper toward Lemma 5.13: the residual unbounded-face goal follows from
the full identification, with its original binders unchanged. -/
theorem hatUnboundedFaceResidualGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (htrans : Filter.Tendsto (L (hatCodes w h)) Filter.atTop Filter.atTop) :
    hatUnboundedFaceResidualGoal w h hfin :=
  (hatUnboundedFaceIdentificationGoal_iff_residual w h hfin).mp
    (hatUnboundedFaceIdentificationGoal_holds w h hfin htrans)

/-- Helper toward Lemma 5.13: the sole extra walk property in the unbounded
orbit clauses holds almost surely for the actual compressed codes, for every
flow-line-hit witness. This uses only the proved R-code law and code equality, -/
theorem iidCodes_ae_hatCodes_left_transient :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ h : HasFlowLineHits (fun i => ω (i + 1)),
        Filter.Tendsto (L (hatCodes (fun i => ω (i + 1)) h))
          Filter.atTop Filter.atTop := by
  filter_upwards [ae_rCodeSequence_KMSW_properties] with ω hω
  intro h
  have he : rCodeSequence ω = hatCodes (fun i => ω (i + 1)) h := by
    rw [← rCodeSequence_quadrantTrajectory_eq_hatCodes _ h]
    exact rCodeSequence_eq_of_succ_eq _ _ (fun _ => rfl)
  rw [← he]
  exact hω.2.1

/-- Helper toward Lemma 5.13: all six deleted-geometry and face goals hold on
one common iid event, with a single flow-line-hit witness and a single ambient -/
theorem iidCodes_ae_hatDeletedGeometry_faceGoals :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w),
        hatDeletedGeometryPathToAmbientExteriorGoal w hfin ∧
        hatDeletedGeometryRootFaceConnectivityGoal w h hfin ∧
        hatBoundedFaceDeletedGeometryExclusionGoal w hfin ∧
        hatUnboundedFaceResidualGoal w h hfin ∧
        hatUnboundedFaceIdentificationGoal w h hfin ∧
        hatBoundedFaceFiniteBorderGoal w h hfin := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_hatCodes_left_transient]
    with ω hflow hfin htrans
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa only [Nat.zero_add] using hflow 0
  exact ⟨h, hfin,
    hatDeletedGeometryPathToAmbientExteriorGoal_holds _ h hfin,
    hatDeletedGeometryRootFaceConnectivityGoal_of_flowLineHits _ h hfin,
    hatBoundedFaceDeletedGeometryExclusionGoal_holds _ h hfin,
    hatUnboundedFaceResidualGoal_holds _ h hfin (htrans h),
    hatUnboundedFaceIdentificationGoal_holds _ h hfin (htrans h),
    hatBoundedFaceFiniteBorderGoal_of_flowLineHits _ h hfin⟩

end DirectedDistances.KMSW
