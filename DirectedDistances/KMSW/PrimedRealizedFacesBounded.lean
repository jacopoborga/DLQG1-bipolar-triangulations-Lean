module

public import DirectedDistances.KMSW.PrimedRealizedFaces
public import DirectedDistances.KMSW.MhatPrimeAmbientFace
public import DirectedDistances.KMSW.PrimedKMSWImageSide

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open scoped Topology

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Retain a raw creation cap when all its geometric darts occur in the primed drawing. -/
private theorem retained_creation_cap (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (j : TriangleCreationTime w)
    (hret : ∀ d ∈ stageTriangleDartList w j, primeGeomEdge w hfin hb d.1) :
    ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
      (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
      ∃ F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w)),
        F.val.val =
          ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
        ∀ d : RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb),
          d.val ∈ stageTriangleDartList w j →
          (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders d F.val := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  obtain ⟨F, hF, hborder, _, _⟩ := mhatPrimeTriangleFace_ambient_face w hfin j i hi
  have hopen : IsOpen F.val.val := by
    rw [hF]
    exact isOpen_graphRegion
      ((familyG w (monotone_family_all w) (j.val + 1)).cap i).low_continuous
      ((familyG w (monotone_family_all w) (j.val + 1)).cap i).high_continuous
  have hedge (e : ℕ)
      (he : e ∈ ({(stageTriangleRecord w j).1, (stageTriangleRecord w j).2.1,
        (stageTriangleRecord w j).2.2} : Multiset ℕ)) : primeGeomEdge w hfin hb e := by
    rw [← stageTriangleDartTriple_edges_eq_record w j] at he
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;>
      exact hret _ (by simp only [stageTriangleDartList, List.mem_cons,
        List.not_mem_nil, or_false]; tauto)
  have htrace (e : ℕ) (he : primeGeomEdge w hfin hb e) :
      stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1)) e ⊆ Q.image := by
    intro z hz
    unfold stageEdgeTrace at hz
    split_ifs at hz with ha
    · refine Or.inr ⟨⟨(e, false), he⟩, ?_⟩
      change z ∈ (P.arc (e, false)).image
      rw [familyDrawing_arc w hfin (monotone_family_all w)
        (j.val + 1) (⟨e, ha⟩, false)]
      exact hz
    · exact hz.elim
  have hfront : frontier F.val.val ⊆ Q.image := by
    rw [hF, creationCap_frontier_eq_traces w j i hi]
    apply Set.union_subset
    · exact Set.union_subset
        (htrace _ (hedge _ (by simp))) (htrace _ (hedge _ (by simp)))
    · exact htrace _ (hedge _ (by simp))
  obtain ⟨G, hG⟩ := planeFace_survives P Q F hopen
    (mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w)) hfront
  refine ⟨i, hi, G, hG.trans hF, ?_⟩
  intro d hd
  exact dartBorders_transport P Q F.val G.val d.val d hG
    (mhatPrimeDrawing_arc w hfin hb (monotone_family_all w) d)
    (hborder d.val hd)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Map a primed creation triangle to its ambient edge multiset. -/
private theorem primed_creation_record_image (w : ℕ → Fin 3)
    (h : HasFlowLineHits w)
    (j : TriangleCreationTime (primedCode (primedSimInput w) h)) :
    ∃ J : TriangleCreationTime w,
      ({primedLimitEdgeMap w h (stageTriangleRecord _ j).1,
        primedLimitEdgeMap w h (stageTriangleRecord _ j).2.1,
        primedLimitEdgeMap w h (stageTriangleRecord _ j).2.2} : Multiset ℕ) =
      {(stageTriangleRecord w J).1, (stageTriangleRecord w J).2.1,
        (stageTriangleRecord w J).2.2} := by
  let u := primedCode (primedSimInput w) h
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index u j
  have hm : stageTriangleRecord u j ∈
      (kmswMissingRootStage u (j.val + 1)).triangles := by
    rw [(kmswMissingRootStage_agree u (j.val + 1)).2.2.2.2.2.1]
    exact hi ▸ List.get_mem _ i
  let t : PrimedLocalTri w h := ⟨stageTriangleRecord u j, j.val + 1, hm⟩
  obtain ⟨_, _, _, _, _, htri, _⟩ := primedKMSW_imageSide w h
  obtain ⟨n, t', ht', hset⟩ := htri t
  rw [← stageTriangleTimes_records w n] at ht'
  obtain ⟨J, _, hJ⟩ := List.mem_map.mp ht'
  refine ⟨J, ?_⟩
  rw [← hJ] at hset
  exact hset.symm

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Each primed creation triangle has a retained ambient creation cap with the source -/
theorem primedCreationTriangle_ambientCap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (j : TriangleCreationTime (primedCode (primedSimInput w) h)) :
    ∃ J : TriangleCreationTime w,
      ({primedLimitEdgeMap w h (stageTriangleRecord _ j).1,
        primedLimitEdgeMap w h (stageTriangleRecord _ j).2.1,
        primedLimitEdgeMap w h (stageTriangleRecord _ j).2.2} : Multiset ℕ) =
      {(stageTriangleRecord w J).1, (stageTriangleRecord w J).2.1,
        (stageTriangleRecord w J).2.2} ∧
      ∃ i : Fin (kmswStage w (J.val + 1)).triangles.length,
        (kmswStage w (J.val + 1)).triangles.get i = stageTriangleRecord w J ∧
        ∃ F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w)),
          F.val.val =
            ((familyG w (monotone_family_all w) (J.val + 1)).cap i).region ∧
          ∀ d : RestrictedDart (ℕ × Bool) (primeDartSet w hfin hb),
            d.val ∈ stageTriangleDartList w J →
            (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders d F.val := by
  obtain ⟨J, hset⟩ := primed_creation_record_image w h j
  have hids : (↑((stageTriangleDartList _ j).map
      (fun d => primedLimitEdgeMap w h d.1)) : Multiset ℕ) =
      {(stageTriangleRecord w J).1, (stageTriangleRecord w J).2.1,
        (stageTriangleRecord w J).2.2} := by
    have hh := congrArg (Multiset.map (primedLimitEdgeMap w h))
      (stageTriangleDartTriple_edges_eq_record _ j)
    have hh' : (↑((stageTriangleDartList _ j).map
        (fun d => primedLimitEdgeMap w h d.1)) : Multiset ℕ) =
        {primedLimitEdgeMap w h (stageTriangleRecord _ j).1,
          primedLimitEdgeMap w h (stageTriangleRecord _ j).2.1,
          primedLimitEdgeMap w h (stageTriangleRecord _ j).2.2} := by
      change ({primedLimitEdgeMap w h (stageTriangleDartTriple _ j).1.1,
        primedLimitEdgeMap w h (stageTriangleDartTriple _ j).2.1.1,
        primedLimitEdgeMap w h (stageTriangleDartTriple _ j).2.2.1} : Multiset ℕ) = _
      simpa using hh
    exact hh'.trans hset
  have hret : ∀ d ∈ stageTriangleDartList w J, primeGeomEdge w hfin hb d.1 := by
    intro d hd
    have he : d.1 ∈ ({(stageTriangleRecord w J).1,
        (stageTriangleRecord w J).2.1, (stageTriangleRecord w J).2.2} : Multiset ℕ) := by
      rw [← stageTriangleDartTriple_edges_eq_record w J]
      simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> simp
    rw [← hids] at he
    change d.1 ∈ (stageTriangleDartList _ j).map
      (fun a => primedLimitEdgeMap w h a.1) at he
    obtain ⟨a, _, ha⟩ := List.mem_map.mp he
    exact (primeGeomEdge_iff_primedLimitEdge w hfin hb h d.1).mpr ⟨a.1, ha⟩
  obtain ⟨i, hi, F, hF, hborders⟩ := retained_creation_cap w hfin hb J hret
  refine ⟨J, hset, i, hi, F, hF, ?_⟩
  intro d hd
  exact hborders d hd

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Unclosed containment step: each primed triangle dart's image must be a member of the
oriented dart list of one ambient creation triangle. This asserts membership, not an
ordered dart correspondence. -/
@[expose] def primedCreationTriangle_orientedImageGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : Prop :=
  let u := primedCode (primedSimInput w) h
  let H := primedGeometricDartEquiv w h hfin hb
  ∀ j : TriangleCreationTime u, ∃ J : TriangleCreationTime w,
    ∀ d ∈ stageTriangleDartList u j, (H d).val ∈ stageTriangleDartList w J

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Unclosed deletion-separation step: each bounded face of the primed drawing must -/
@[expose] def primedBoundedFace_ambientFaceGoal (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) : Prop :=
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  ∀ F : PlaneFaces Q, ∃ G : PlaneFaces P, G.val.val = F.val.val

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Unclosed ambient-face classification step for the two-sided drawing. -/
@[expose] def primedAmbientBoundedFace_creationCapGoal (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) : Prop :=
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  ∀ G : PlaneFaces P, ∃ J : TriangleCreationTime w,
    ∃ i : Fin (kmswStage w (J.val + 1)).triangles.length,
      (kmswStage w (J.val + 1)).triangles.get i = stageTriangleRecord w J ∧
      G.val.val = ((familyG w (monotone_family_all w) (J.val + 1)).cap i).region

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Unclosed reverse image step from retained ambient caps to primed KMSW triangles.
The present result gives only the forward image of primed triangles. -/
@[expose] def primedRetainedAmbientCap_preimageGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : Prop :=
  let u := primedCode (primedSimInput w) h
  ∀ J : TriangleCreationTime w,
    (∀ d ∈ stageTriangleDartList w J, primeGeomEdge w hfin hb d.1) →
    ∃ j : TriangleCreationTime u,
      ({primedLimitEdgeMap w h (stageTriangleRecord u j).1,
        primedLimitEdgeMap w h (stageTriangleRecord u j).2.1,
        primedLimitEdgeMap w h (stageTriangleRecord u j).2.2} : Multiset ℕ) =
      {(stageTriangleRecord w J).1, (stageTriangleRecord w J).2.1,
        (stageTriangleRecord w J).2.2}

end DirectedDistances.KMSW
