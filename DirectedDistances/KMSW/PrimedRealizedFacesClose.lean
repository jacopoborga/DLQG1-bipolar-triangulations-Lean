module

public import DirectedDistances.KMSW.PrimedRealizedFacesExternal
public import DirectedDistances.KMSW.PrimedRealizedFacesBounded
import DirectedDistances.KMSW.GluingBoundaryOrder
import DirectedDistances.Recursive.HLRLdpFinal
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.KMSW.HatRealizedFaces
import DirectedDistances.KMSW.HatRealizedFacesComplete








public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open Filter Set
open scoped Topology

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The identified LL vertices force arbitrarily negative primed horizontal levels. -/
private theorem primedClose_L_unbounded_below (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hb : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, L (primedCode (primedSimInput w) h) n ≤ a := by
  intro a
  let u := primedCode (primedSimInput w) h
  let i := Int.toNat (-a)
  obtain ⟨n, hn⟩ :=
    (DirectedDistances.Recursive.primedEntryOuterLLVertexIdentification_proved w h hb i).exists
  obtain ⟨v, hv, _⟩ := hn
  have hi : i < (kmswStage u n).LL.length := by
    have hh := List.getElem?_eq_some_iff.mp hv
    obtain ⟨hh, _⟩ := hh
    simpa only [List.length_map, List.length_reverse] using hh
  have hlen := kmswStage_LL_length u n
  obtain ⟨j, _, hj⟩ := runningMin_attained (L u) n
  refine ⟨j, ?_⟩
  change minL u n = L u j at hj
  have hai : -a ≤ (i : ℤ) := Int.self_le_toNat (-a)
  change L u j ≤ a
  omega

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every dart in the marked external orbit is persistently on the stage exterior. -/
private theorem primedClose_externalOrbit_persistent (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w) (d : ℕ × Bool)
    (hd : (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d) :
    limitExternalDart (primedCode (primedSimInput w) h) d := by
  classical
  let u := primedCode (primedSimInput w) h
  let hf := primedCode_finiteIncidence w h hfin
  let f := kmswInfFaceSucc u hf
  by_contra he
  have hfinite := (finiteFaceOrbit_iff_not_external u hf d).mpr he
  have hsub : {e | f.SameCycle futureMapOuterDart e} ⊆ {e | f.SameCycle d e} := by
    intro e he
    exact hd.symm.trans he
  have hroot := (finiteFaceOrbit_iff_not_external u hf futureMapOuterDart).mp
    (hfinite.subset hsub)
  exact hroot (futureMapOuterDart_external u)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Persistent primed exterior darts use only LL, UR, or the C18 root. -/
private theorem primedClose_external_boundary_stacks (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hd : limitExternalDart (primedCode (primedSimInput w) h) d) :
    d.1 = 0 ∨ ∃ N, ∀ n ≥ N,
      d.1 ∈ (kmswStage (primedCode (primedSimInput w) h) n).LL ∨
        d.1 ∈ (kmswStage (primedCode (primedSimInput w) h) n).UR := by
  let u := primedCode (primedSimInput w) h
  obtain ⟨N, hN⟩ := hd
  obtain ⟨M, hM⟩ := kmswRun_UL_eventually_absent u
    (primedClose_L_unbounded_below w h hb) d.1
  by_cases hz : d.1 = 0
  · exact Or.inl hz
  right
  refine ⟨max N M, fun n hn => ?_⟩
  obtain ⟨ha, ho⟩ := hN n ((Nat.le_max_left _ _).trans hn)
  have ho' := (kmswStage_isOuter_iff_boundary u n (⟨d.1, ha⟩, d.2)).mp ho
  simp only [List.mem_append] at ho'
  rcases ho' with ⟨_, hUL | hUR⟩ | ⟨_, hLL | hLR⟩
  · exact (hM n ((Nat.le_max_right _ _).trans hn) hUL).elim
  · exact Or.inr hUR
  · exact Or.inl hLL
  · rw [primedStage_LR_eq_root] at hLR
    exact (hz (List.mem_singleton.mp hLR)).elim

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every persistent primed exterior edge is missing, with the root handled by C18. -/
private theorem primedClose_persistent_missing (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hb : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hd : limitExternalDart (primedCode (primedSimInput w) h) d) :
    ¬ PrimedEdgePresent w h d.1 := by
  rcases primedClose_external_boundary_stacks w h hb d hd with hz | ⟨N, hN⟩
  · rw [hz]
    exact primedLimitRoot_not_primedPresent w h
  intro hp
  have hne : d.1 ≠ 0 := fun hz => primedLimitRoot_not_primedPresent w h (hz ▸ hp)
  obtain ⟨M, hM⟩ := hp.eventually_present w h
  let n := max N M
  obtain ⟨ha, hp⟩ := hM n (Nat.le_max_right _ _)
  have hagree := kmswMissingRootStage_agree (primedCode (primedSimInput w) h) n
  have ha' : d.1 < (kmswStage (primedCode (primedSimInput w) h) n).nextEdge := by
    rw [← hagree.2.1]
    exact ha
  have hp' : (kmswStage (primedCode (primedSimInput w) h) n).present d.1 = true :=
    (hagree.2.2.2.2.1 d.1 hne).symm.trans hp
  have hm := ((kmswStage_status (primedCode (primedSimInput w) h) n).1 d.1 ha').mpr
    ((hN n (Nat.le_max_left _ _)).elim Or.inr Or.inl)
  rw [hp'] at hm
  cases hm

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The combinatorial external-orbit missing-tag goal is proved without added premises. -/
theorem primedExternalOrbitCodeMissingGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : primedExternalOrbitCodeMissingGoal w h hfin hb := by
  intro d hd
  exact primedClose_persistent_missing w h hb d
    (primedClose_externalOrbit_persistent w h hfin d hd)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Transport the proved missing tags to the retained primed geometric edges. -/
theorem primedExternalOrbitMissingGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : primedExternalOrbitMissingGoal w h hfin hb :=
  (primedExternalOrbitMissing_iff_codeMissing w h hfin hb).mpr
    (primedExternalOrbitCodeMissingGoal_holds w h hfin hb)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Bounded face sets cannot satisfy quantified unboundedness. -/
private theorem bounded_not_unbounded {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F : PlaneFaces P) : ¬ P.IsUnbounded F.val := by
  obtain ⟨R, hR⟩ := F.property.subset_closedBall (0 : ℂ)
  intro h
  obtain ⟨z, hz, hnorm⟩ := h R
  have hzR : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
  exact (not_lt_of_ge hzR) hnorm

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every ambient bounded face is a recorded creation cap; this closes the ambient
classification subgoal independently of primed deletion separation. -/
theorem primedAmbientBoundedFace_creationCapGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    : primedAmbientBoundedFace_creationCapGoal w hfin := by
  intro F
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := familyQ w (monotone_family_all w)
  let G := familyG w (monotone_family_all w)
  let E := monotoneLimitExterior Q G
  have himage : P.image = ⋃ n, (Q n).image :=
    monotoneFamilyDrawing_image w hfin (monotone_family_all w)
  obtain ⟨z, hz, hF⟩ := F.val.property
  have hzF : z ∈ F.val.val := hF ▸ mem_connectedComponentIn hz
  have hzE : z ∉ E := by
    intro hzE
    have hconn := (monotoneLimitExterior_isPathConnected_twoSided w hfin
      (hatBoundaryHitWitnesses w h) Q G).isConnected
    have havoid : E ⊆ P.imageᶜ := by
      intro a ha hPa
      rw [himage] at hPa
      obtain ⟨n, hn⟩ := mem_iUnion.mp hPa
      exact (disjoint_left.mp (monotoneLimitExterior_disjoint_stageImage Q G n)) ha hn
    have hEF : E ⊆ F.val.val := by
      rw [hF]
      exact hconn.isPreconnected.subset_connectedComponentIn hzE havoid
    apply bounded_not_unbounded P F
    intro R
    obtain ⟨a, ha, hRa⟩ := monotoneLimitExterior_unbounded_twoSided Q G R
    exact ⟨a, hEF ha, hRa⟩
  have hzUnion : z ∈ monotoneStageRegionUnion Q G := not_not.mp hzE
  have hzTrace : z ∉ monotoneLayoutTraceUnion Q := by
    intro hzT
    apply hz
    exact himage.symm ▸ hzT
  obtain ⟨n, i, hzcap⟩ := monotoneStageRegionUnion_mem_cap_of_not_trace Q G hzUnion hzTrace
  obtain ⟨F', hF'⟩ := monotoneFamily_cap_planeFace w hfin n i
  have heq : F.val = F'.val := P.faces_eq_of_mem hzF (hF'.symm ▸ hzcap)
  let tri := (kmswStage w n).triangles.get i
  have ht : tri ∈ (kmswStage w n).triangles := List.get_mem _ i
  rw [← stageTriangleTimes_records] at ht
  obtain ⟨j, _, hj⟩ := List.mem_map.mp ht
  obtain ⟨k, hk⟩ := stageTriangleRecord_fin_index w j
  have hcap : ((G n).cap i).region = ((G (j.val + 1)).cap k).region := by
    apply monotone_cap_region_eq w (G n) (G (j.val + 1)) i k (hj.symm.trans hk.symm)
    intro e he
    have hb := triBound_stage w n _ (List.get_mem _ i)
    have hb' := triBound_stage w (j.val + 1) _ (List.get_mem _ k)
    have he' : e ∈ [((kmswStage w (j.val + 1)).triangles.get k).1,
        ((kmswStage w (j.val + 1)).triangles.get k).2.1,
        ((kmswStage w (j.val + 1)).triangles.get k).2.2] := by
      rwa [hk, hj]
    have hbound : e < (kmswStage w n).nextEdge := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hb.1
      · exact hb.2.1
      · exact hb.2.2
    have hbound' : e < (kmswStage w (j.val + 1)).nextEdge := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl
      · exact hb'.1
      · exact hb'.2.1
      · exact hb'.2.2
    simp only [stageEdgeTrace, dite_eq_left hbound, dite_eq_left hbound']
    rw [← familyDrawing_arc w hfin (monotone_family_all w) n (⟨e, hbound⟩, false),
      ← familyDrawing_arc w hfin (monotone_family_all w) (j.val + 1)
        (⟨e, hbound'⟩, false)]
  exact ⟨j, k, hk, (congrArg Subtype.val heq).trans (hF'.trans hcap)⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The remaining separation step says that bounded primed faces avoid deleted ambient
geometry. The drawing retains beta-zero arcs, even though those edges are missing.
This proposition is open and is not assumed by any unconditional result here. -/
@[expose] def primedBoundedFace_deletedGeometryExclusionGoal (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) : Prop :=
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  ∀ F : PlaneFaces Q, Disjoint F.val.val P.image

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The ambient-face goal is exactly exclusion of deleted geometry from bounded faces.
Neither equivalent separation proposition is asserted unconditionally. -/
theorem primedBoundedFace_ambientFaceGoal_iff_deletedGeometryExclusion
    (w : ℕ → Fin 3) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedBoundedFace_ambientFaceGoal w hfin hb ↔
      primedBoundedFace_deletedGeometryExclusionGoal w hfin hb := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  constructor
  · intro hamb F
    obtain ⟨G, hG⟩ := hamb F
    apply Set.disjoint_left.mpr
    intro z hz hzP
    exact P.face_subset_compl G.val (hG.symm ▸ hz) hzP
  · intro hexcl F
    obtain ⟨z, hz, hF⟩ := F.val.property
    have hzF : z ∈ F.val.val := hF ▸ mem_connectedComponentIn hz
    have havoid : F.val.val ⊆ P.imageᶜ := by
      intro a ha haP
      exact Set.disjoint_left.mp (hexcl F) ha haP
    have hzP : z ∈ P.imageᶜ := havoid hzF
    let C := connectedComponentIn P.imageᶜ z
    have hFC : F.val.val ⊆ C := by
      have hc : IsPreconnected F.val.val := by
        rw [hF]
        exact isPreconnected_connectedComponentIn
      exact hc.subset_connectedComponentIn hzF havoid
    have hCF : C ⊆ F.val.val := by
      rw [hF]
      exact connectedComponentIn_mono z (by
        intro a ha haQ
        exact ha (mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w) haQ))
    have heq : C = F.val.val := Set.Subset.antisymm hCF hFC
    have hbounded : Bornology.IsBounded C := by
      rw [heq]
      exact F.property
    exact ⟨⟨⟨C, z, hzP, rfl⟩, hbounded⟩, heq⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Retain a raw creation cap when all its geometric darts occur in the primed drawing. -/
private theorem close_retained_creation_cap (w : ℕ → Fin 3)
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
Containment of the three oriented dart images suffices for oriented bordering.
This is an implication from the named open image goal, not its assumption as a
premise of any completed paper result. -/
theorem primedCreationTriangle_orientedImageGoal_implies_orientedBorders
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedCreationTriangle_orientedImageGoal w h hfin hb →
      primedCreationTriangle_orientedBordersGoal w h hfin hb := by
  classical
  intro himage j
  let u := primedCode (primedSimInput w) h
  let H := primedGeometricDartEquiv w h hfin hb
  let L := (stageTriangleDartList u j).map (fun d => (H d).val)
  obtain ⟨J, hJ⟩ := himage j
  have hnd : L.Nodup := (stageTriangleDartList_nodup u j).map
    (Subtype.val_injective.comp H.injective)
  have hsub : L.toFinset ⊆ (stageTriangleDartList w J).toFinset := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact List.mem_toFinset.mpr (hJ a ha)
  have heq : L.toFinset = (stageTriangleDartList w J).toFinset := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [List.toFinset_card_of_nodup hnd,
      List.toFinset_card_of_nodup (stageTriangleDartList_nodup w J)]
    simp only [L, List.length_map, stageTriangleDartList, List.length_cons,
      List.length_nil, Nat.le_refl]
  have hret : ∀ d ∈ stageTriangleDartList w J, primeGeomEdge w hfin hb d.1 := by
    intro d hd
    have hd' : d ∈ L := by
      apply List.mem_toFinset.mp
      rw [heq]
      exact List.mem_toFinset.mpr hd
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hd'
    have hp := (H a).property
    rw [ha] at hp
    exact hp
  obtain ⟨_, _, F, _, hborder⟩ := close_retained_creation_cap w hfin hb J hret
  exact ⟨F, fun d hd => hborder (H d) (hJ d hd)⟩

end DirectedDistances.KMSW
