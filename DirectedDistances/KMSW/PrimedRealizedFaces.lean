module

public import DirectedDistances.KMSW.PrimedLimitRotation
public import DirectedDistances.PaperProofs.Section5.FlowTrianglePrimePlaneFace
import DirectedDistances.KMSW.PrimedKMSWImageSide

/-! Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Finite primed face orbits have triangular bounded frontiers. Source flow triangles
also have oriented bordering; the remaining face obligations are isolated below. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open scoped Topology

private theorem reverse_trace_subset (p : Polyline) : p.reverse.image ⊆ p.image := by
  rintro z (hz | ⟨i, hi, hz⟩)
  · have hz' : z = p.finish := by
      simpa only [Polyline.start_reverse, Set.mem_singleton_iff] using hz
    rw [hz', ← p.point_last_eq_finish]
    by_cases hlen : 2 ≤ p.points.length
    · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
      have hidx : p.points.length - 2 + 1 = p.points.length - 1 := by omega
      rw [Polyline.segmentAt, hidx]
      exact right_mem_segment ℝ _ _
    · have hlen1 : p.points.length = 1 := by
        have := List.length_pos_iff.mpr p.nonempty
        omega
      simp only [hlen1, Nat.sub_self, Polyline.point_zero_eq_start]
      exact Or.inl rfl
  · have hi' : i + 1 < p.points.length := by
      simpa only [Polyline.reverse, List.length_reverse] using hi
    have hrev : ∀ j, j < p.points.length →
        p.reverse.point j = p.point (p.points.length - 1 - j) := by
      intro j hj
      have hj' : p.points.length - 1 - j < p.points.length := by omega
      change p.points.reverse.getD j p.reverse.start =
        p.points.getD (p.points.length - 1 - j) p.start
      rw [List.getD_reverse j hj]
      rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj']
      rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj']
    have hidx : p.points.length - 1 - (i + 1) + 1 = p.points.length - 1 - i := by
      omega
    refine Or.inr ⟨p.points.length - 1 - (i + 1), by omega, ?_⟩
    simp only [Polyline.segmentAt, hrev i (by omega), hrev (i + 1) hi'] at hz
    simpa only [Polyline.segmentAt, hidx, segment_symm] using hz

private theorem reverse_trace (p : Polyline) : p.reverse.image = p.image := by
  apply Set.Subset.antisymm (reverse_trace_subset p)
  simpa only [Polyline.reverse_reverse] using reverse_trace_subset p.reverse

private theorem ambient_trace_side (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (d : ℕ × Bool) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    (P.arc d).image = (P.arc (d.1, false)).image := by
  dsimp only
  rcases d with ⟨e, b⟩
  cases b
  · rfl
  · let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    have heq : P.arc (e, true) = (P.arc (e, false)).reverse := P.arc_flip (e, false)
    rw [heq, reverse_trace]

private theorem retained_creation_face (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (j : TriangleCreationTime w)
    (hret : ∀ d ∈ stageTriangleDartList w j, primeGeomEdge w hfin hb d.1) :
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∃ i : Fin (kmswStage w (j.val + 1)).triangles.length,
      (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
      ∃ F : PlaneFaces Q,
        F.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
        ∀ d, ∀ hd : d ∈ stageTriangleDartList w j,
          Q.dartBorders ⟨d, hret d hd⟩ F.val := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  obtain ⟨F, hF, hborder⟩ := stageTriangleDarts_border_creation_cap w hfin j i hi
  have hopen : IsOpen F.val.val := by
    rw [hF]
    exact isOpen_graphRegion
      ((familyG w (monotone_family_all w) (j.val + 1)).cap i).low_continuous
      ((familyG w (monotone_family_all w) (j.val + 1)).cap i).high_continuous
  have hedge (e : ℕ) (he : e ∈ ({(stageTriangleRecord w j).1,
      (stageTriangleRecord w j).2.1, (stageTriangleRecord w j).2.2} : Multiset ℕ)) :
      primeGeomEdge w hfin hb e := by
    rw [← stageTriangleDartTriple_edges_eq_record w j] at he
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at he
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
    · exact Set.union_subset (htrace _ (hedge _ (by simp)))
        (htrace _ (hedge _ (by simp)))
    · exact htrace _ (hedge _ (by simp))
  obtain ⟨G, hG⟩ := planeFace_survives P Q F hopen
    (mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w)) hfront
  refine ⟨i, hi, G, hG.trans hF, fun d hd => ?_⟩
  exact dartBorders_transport P Q F.val G.val d ⟨d, hret d hd⟩ hG
    (mhatPrimeDrawing_arc w hfin hb (monotone_family_all w) _) (hborder d hd)

private theorem carrier_step_of_ambient_step (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (d e : {d // d ∈ primeDartSet w hfin hb})
    (hs : kmswInfFaceSucc w hfin d.val = e.val) :
    let H := primedGeometricDartEquiv w h hfin hb
    kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin) (H.symm d) = H.symm e := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let S := primeDartSet w hfin hb
  let H := primedGeometricDartEquiv w h hfin hb
  let τ := drawingFirstReturnPerm P S
  have hr : kmswInfRot w hfin e.val = futureMapEdgeInv d.val := by
    change (kmswInfRot w hfin).symm (futureMapEdgeInv d.val) = e.val at hs
    rw [← hs, Equiv.apply_symm_apply]
  have ht : τ e = restrictedFlip P S (primeDartSet_flip_closed w hfin hb) d := by
    apply Subtype.ext
    exact (drawingFirstReturn_eq_next P S e (by
      rw [hr]; exact (primeDartSet_flip_closed w hfin hb d.val).mp d.property)).trans hr
  apply H.injective
  rw [primedGeometricDartEquiv_faceSuccessor]
  change τ.symm (restrictedFlip P S (primeDartSet_flip_closed w hfin hb)
    (H (H.symm d))) = H (H.symm e)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← ht, Equiv.symm_apply_apply]

private theorem outerWord_sameCycle (w : ℕ → Fin 3) (n : ℕ)
    (a b : StageDart (kmswStage w n).nextEdge)
    (ha : a ∈ stageOuterWord w n) (hb : b ∈ stageOuterWord w n) :
    (stageOuterWord w n).formPerm.SameCycle a b := by
  generalize hl : stageOuterWord w n = l at *
  have hnd : l.Nodup := hl ▸ stageOuterWord_nodup w n
  cases l with
  | nil => exact (List.not_mem_nil ha).elim
  | cons x xs =>
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      have hA : ((x :: xs).formPerm ^ i) x = (x :: xs)[i] := by
        simpa only [Nat.mod_eq_of_lt hi] using
          List.formPerm_pow_apply_head x xs hnd i
      have hB : ((x :: xs).formPerm ^ j) x = (x :: xs)[j] := by
        simpa only [Nat.mod_eq_of_lt hj] using
          List.formPerm_pow_apply_head x xs hnd j
      exact (Equiv.Perm.SameCycle.symm ⟨i, hA⟩).trans ⟨j, hB⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A finite limiting face orbit contains a recorded creation dart. This argument
uses finite incidence alone, so it applies to the primed code without a sign -/
theorem primedRealizedFaces_finiteOrbit_triangle (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc w hfin).SameCycle d e}.Finite) :
    ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  classical
  let f := kmswInfFaceSucc w hfin
  let S := {e | f.SameCycle d e}
  have hS : S.Finite := hfinite
  have hstage (e : ℕ × Bool) := kmswInfFaceSucc_eventually_eq_stage w hfin e
  let cutoff : ℕ × Bool → ℕ := fun e => (hstage e).choose
  obtain ⟨B, hB⟩ := (hS.image cutoff).bddAbove
  have htimes : ((fun n => (act w n, false)) ⁻¹' S).Finite :=
    Set.Finite.preimage (fun _ _ _ _ he =>
      CutConverse.act_injective w (congrArg Prod.fst he)) hS
  obtain ⟨A, hA⟩ := htimes.bddAbove
  let n := max B (A + 1)
  have hn : B ≤ n := Nat.le_max_left _ _
  have hd : d ∈ S := Equiv.Perm.SameCycle.refl f d
  have hstep (e : ℕ × Bool) (he : e ∈ S) :=
    (hstage e).choose_spec n ((hB (Set.mem_image_of_mem cutoff he)).trans hn)
  obtain ⟨halloc, _⟩ := hstep d hd
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, halloc⟩, d.2)
  rcases stage_dart_partition w n x with hout | ⟨j, hj, _⟩
  · let l := stageOuterWord w n
    have hmem (k : ℕ) : (l.formPerm ^ k) x ∈ l := by
      induction k with
      | zero => exact hout
      | succ k ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact List.formPerm_apply_mem_of_mem ih
    have hproj (k : ℕ) :
        (((l.formPerm ^ k) x).1.val, ((l.formPerm ^ k) x).2) ∈ S := by
      induction k with
      | zero => exact hd
      | succ k ih =>
          let y := (l.formPerm ^ k) x
          obtain ⟨hy, hsy⟩ := hstep (y.1.val, y.2) ih
          have hyEq : (⟨y.1.val, hy⟩, y.2) = y := rfl
          rw [hyEq, stageOuterWord_faceSucc w n y (hmem k)] at hsy
          rw [pow_succ', Equiv.Perm.mul_apply]
          change ((l.formPerm y).1.val, (l.formPerm y).2) ∈ S
          rw [← hsy]
          exact Equiv.Perm.SameCycle.apply_right ih
    let a : StageDart (kmswStage w n).nextEdge :=
      (⟨act w n, act_lt_nextEdge w (Nat.le_refl n)⟩, false)
    have ha : a ∈ stageOuterWord w n := by
      apply (stageOuterWord_mem_iff w n a).mpr
      exact Or.inl ⟨rfl, Or.inl (List.mem_of_getLast? (kmswStage_UL_nonempty_active_last w n).2)⟩
    obtain ⟨k, hk⟩ := (outerWord_sameCycle w n x a hout ha).exists_nat_pow_eq
    have hactive := hproj k
    rw [hk] at hactive
    have hbound : n ≤ A := hA hactive
    dsimp only [n] at hbound
    omega
  · exact ⟨j, hj.2⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every source flow triangle is a three-cycle of the compressed primed carrier whose
three geometric dart images border one bounded plane face of the primed drawing. -/
theorem primedFlowTriangle_realized (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (k : ℕ) (hk : 1 ≤ k) :
    let r := sourceFlowNR w h (k - 1)
    let t := sourceFlowNL w h (k - 1)
    let e := if k = 1 then (kmswStage w (t - 1)).nextEdge + 1 else act w (r - 1)
    let H := primedGeometricDartEquiv w h hfin hb
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∃ (F : PlaneFaces Q) (a b c : ℕ × Bool),
      FaceSucc3Cycle (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)) a b c ∧
      ({(H a).val.1, (H b).val.1, (H c).val.1} : Multiset ℕ) =
        {act w (t - 1), act w t, e} ∧
      Q.dartBorders (H a) F.val ∧ Q.dartBorders (H b) F.val ∧
        Q.dartBorders (H c) F.val := by
  let H := primedGeometricDartEquiv w h hfin hb
  obtain ⟨j, _, _, hrecord, _, _⟩ := flowLineTimes_triangle_creation_record w h k hk
  obtain ⟨hold, hnew, hthird⟩ := flowTriangle_three_retained w hfin hb h k hk
  have hret : ∀ d ∈ stageTriangleDartList w j, primeGeomEdge w hfin hb d.1 := by
    intro d hd
    have hm : d.1 ∈ ({(stageTriangleRecord w j).1,
        (stageTriangleRecord w j).2.1, (stageTriangleRecord w j).2.2} : Multiset ℕ) := by
      rw [← stageTriangleDartTriple_edges_eq_record w j]
      simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> simp
    rw [hrecord] at hm
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
    rcases hm with he | he | he
    · exact he ▸ hold
    · exact he ▸ hnew
    · exact he ▸ hthird
  let T := stageTriangleDartTriple w j
  have h1 : T.1 ∈ stageTriangleDartList w j := by simp [stageTriangleDartList, T]
  have h2 : T.2.1 ∈ stageTriangleDartList w j := by simp [stageTriangleDartList, T]
  have h3 : T.2.2 ∈ stageTriangleDartList w j := by simp [stageTriangleDartList, T]
  let x : {d // d ∈ primeDartSet w hfin hb} := ⟨T.1, hret _ h1⟩
  let y : {d // d ∈ primeDartSet w hfin hb} := ⟨T.2.1, hret _ h2⟩
  let z : {d // d ∈ primeDartSet w hfin hb} := ⟨T.2.2, hret _ h3⟩
  obtain ⟨_, _, F, _, hF⟩ := retained_creation_face w hfin hb j hret
  obtain ⟨h12, h23, h31, hn12, hn23, hn31⟩ :=
    kmswInfFaceSucc_stageTriangle_cycle w hfin j
  refine ⟨F, H.symm x, H.symm y, H.symm z, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨carrier_step_of_ambient_step w h hfin hb x y h12,
      carrier_step_of_ambient_step w h hfin hb y z h23,
      carrier_step_of_ambient_step w h hfin hb z x h31, ?_, ?_, ?_⟩
    · intro he; exact hn12 (congrArg Subtype.val (H.symm.injective he))
    · intro he; exact hn23 (congrArg Subtype.val (H.symm.injective he))
    · intro he; exact hn31 (congrArg Subtype.val (H.symm.injective he))
  · change ({(H (H.symm x)).val.1, (H (H.symm y)).val.1,
        (H (H.symm z)).val.1} : Multiset ℕ) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change ({T.1.1, T.2.1.1, T.2.2.1} : Multiset ℕ) = _
    rw [stageTriangleDartTriple_edges_eq_record w j, hrecord]
  · rw [Equiv.apply_symm_apply]; exact hF _ h1
  · rw [Equiv.apply_symm_apply]; exact hF _ h2
  · rw [Equiv.apply_symm_apply]; exact hF _ h3

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
  have hm : stageTriangleRecord u j ∈ (kmswMissingRootStage u (j.val + 1)).triangles := by
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
Every recorded primed triangle has the exact geometric frontier of a bounded
plane face. This assertion concerns arc traces; oriented bordering of each
primed dart is a separate obligation below. -/
theorem primedCreationTriangle_realizedFrontier (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (j : TriangleCreationTime (primedCode (primedSimInput w) h)) :
    let u := primedCode (primedSimInput w) h
    let H := primedGeometricDartEquiv w h hfin hb
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∃ F : PlaneFaces Q,
      frontier F.val.val = ⋃ d ∈ stageTriangleDartList u j, (Q.arc (H d)).image := by
  let u := primedCode (primedSimInput w) h
  let H := primedGeometricDartEquiv w h hfin hb
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨J, hset⟩ := primed_creation_record_image w h j
  have hids : (↑((stageTriangleDartList u j).map
      (fun d => primedLimitEdgeMap w h d.1)) : Multiset ℕ) =
      {(stageTriangleRecord w J).1, (stageTriangleRecord w J).2.1,
        (stageTriangleRecord w J).2.2} := by
    have hh := congrArg (Multiset.map (primedLimitEdgeMap w h))
      (stageTriangleDartTriple_edges_eq_record u j)
    have hh' : (↑((stageTriangleDartList u j).map
        (fun d => primedLimitEdgeMap w h d.1)) : Multiset ℕ) =
        {primedLimitEdgeMap w h (stageTriangleRecord u j).1,
          primedLimitEdgeMap w h (stageTriangleRecord u j).2.1,
          primedLimitEdgeMap w h (stageTriangleRecord u j).2.2} := by
      change ({primedLimitEdgeMap w h (stageTriangleDartTriple u j).1.1,
        primedLimitEdgeMap w h (stageTriangleDartTriple u j).2.1.1,
        primedLimitEdgeMap w h (stageTriangleDartTriple u j).2.2.1} : Multiset ℕ) = _
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
    change d.1 ∈ (stageTriangleDartList u j).map
      (fun a => primedLimitEdgeMap w h a.1) at he
    obtain ⟨a, _, ha⟩ := List.mem_map.mp he
    exact (primeGeomEdge_iff_primedLimitEdge w hfin hb h d.1).mpr ⟨a.1, ha⟩
  obtain ⟨i, hi, F, hF, _⟩ := retained_creation_face w hfin hb J hret
  have htrace (e : ℕ) (he : e < (kmswStage w (J.val + 1)).nextEdge) :
      stageEdgeTrace (familyQ w (monotone_family_all w) (J.val + 1)) e =
        (P.arc (e, false)).image := by
    unfold stageEdgeTrace
    rw [dite_eq_left he]
    exact congrArg Polyline.image
      (familyDrawing_arc w hfin (monotone_family_all w) (J.val + 1)
        (⟨e, he⟩, false)).symm
  have halloc := triBound_stage w (J.val + 1) (stageTriangleRecord w J)
    (hi ▸ List.get_mem _ i)
  have harc (d : ℕ × Bool) :
      (Q.arc (H d)).image = (P.arc (primedLimitEdgeMap w h d.1, false)).image := by
    change (P.arc (primedLimitDartMap w h d)).image = _
    exact ambient_trace_side w hfin (primedLimitDartMap w h d)
  refine ⟨F, ?_⟩
  rw [hF, creationCap_frontier_eq_traces w J i hi,
    htrace _ halloc.1, htrace _ halloc.2.1, htrace _ halloc.2.2]
  ext z
  simp only [Set.mem_union, Set.mem_iUnion]
  have hm (e : ℕ) : e ∈ ({(stageTriangleRecord w J).1,
      (stageTriangleRecord w J).2.1, (stageTriangleRecord w J).2.2} : Multiset ℕ) ↔
      ∃ d ∈ stageTriangleDartList u j, primedLimitEdgeMap w h d.1 = e := by
    rw [← hids]
    exact List.mem_map
  constructor
  · intro hz
    have hex : ∃ e, e ∈ ({(stageTriangleRecord w J).1,
        (stageTriangleRecord w J).2.1, (stageTriangleRecord w J).2.2} : Multiset ℕ) ∧
        z ∈ (P.arc (e, false)).image := by
      rcases hz with (hz | hz) | hz
      · exact ⟨_, by simp, hz⟩
      · exact ⟨_, by simp, hz⟩
      · exact ⟨_, by simp, hz⟩
    obtain ⟨e, he, hz⟩ := hex
    obtain ⟨d, hd, hde⟩ := (hm e).mp he
    refine ⟨d, hd, ?_⟩
    rw [harc, hde]
    exact hz
  · rintro ⟨d, hd, hz⟩
    rw [harc] at hz
    have he := (hm _).mpr ⟨d, hd, rfl⟩
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at he
    rcases he with he | he | he
    · exact Or.inl (Or.inl (he ▸ hz))
    · exact Or.inl (Or.inr (he ▸ hz))
    · exact Or.inr (he ▸ hz)

private theorem cycle3_sameCycle_iff {D : Type*} (f : Equiv.Perm D)
    (a b c : D) (hc : FaceSucc3Cycle f a b c) (d e : D)
    (hd : d = a ∨ d = b ∨ d = c) :
    f.SameCycle d e ↔ e = a ∨ e = b ∨ e = c := by
  obtain ⟨hab, hbc, hca, _, _, _⟩ := hc
  have hmem (z : ℤ) : (f ^ z) a = a ∨ (f ^ z) a = b ∨ (f ^ z) a = c := by
    induction z using Int.induction_on with
    | zero => exact Or.inl rfl
    | succ n ih =>
        rw [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
        rcases ih with ha | hb | hc
        · exact Or.inr (Or.inl ((congrArg f ha).trans hab))
        · exact Or.inr (Or.inr ((congrArg f hb).trans hbc))
        · exact Or.inl ((congrArg f hc).trans hca)
    | pred n ih =>
        have hn : -(n : ℤ) - 1 = -1 + -(n : ℤ) := by omega
        rw [hn, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
        have hba : f.symm b = a := (f.symm_apply_eq).mpr hab.symm
        have hcb : f.symm c = b := (f.symm_apply_eq).mpr hbc.symm
        have hac : f.symm a = c := (f.symm_apply_eq).mpr hca.symm
        rcases ih with ha | hb | hc
        · exact Or.inr (Or.inr ((congrArg f.symm ha).trans hac))
        · exact Or.inl ((congrArg f.symm hb).trans hba)
        · exact Or.inr (Or.inl ((congrArg f.symm hc).trans hcb))
  have hab' : f.SameCycle a b := ⟨1, by simpa using hab⟩
  have hbc' : f.SameCycle b c := ⟨1, by simpa using hbc⟩
  have had : f.SameCycle a d := by
    rcases hd with hd | hd | hd
    · rw [hd]
    · rw [hd]; exact hab'
    · rw [hd]; exact hab'.trans hbc'
  constructor
  · intro he
    obtain ⟨z, hz⟩ := had.trans he
    exact hz ▸ hmem z
  · intro he
    apply had.symm.trans
    rcases he with he | he | he
    · rw [he]
    · rw [he]; exact hab'
    · rw [he]; exact hab'.trans hbc'

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every finite primed carrier face orbit is exactly a recorded three-cycle and
its geometric traces are exactly the frontier of a bounded primed plane face.
Oriented dart bordering for general triangles is not claimed by this theorem. -/
theorem primedFiniteFaceOrbit_realizedFrontier (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle d e}.Finite) :
    let u := primedCode (primedSimInput w) h
    let f := kmswInfFaceSucc u (primedCode_finiteIncidence w h hfin)
    let H := primedGeometricDartEquiv w h hfin hb
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∃ (j : TriangleCreationTime u) (F : PlaneFaces Q),
      d ∈ stageTriangleDartList u j ∧
      FaceSucc3Cycle f (stageTriangleDartTriple u j).1
        (stageTriangleDartTriple u j).2.1 (stageTriangleDartTriple u j).2.2 ∧
      (∀ e, f.SameCycle d e ↔ e ∈ stageTriangleDartList u j) ∧
      frontier F.val.val = ⋃ e ∈ stageTriangleDartList u j, (Q.arc (H e)).image := by
  let u := primedCode (primedSimInput w) h
  let hf := primedCode_finiteIncidence w h hfin
  obtain ⟨j, hd⟩ := primedRealizedFaces_finiteOrbit_triangle u hf d hfinite
  obtain ⟨F, hF⟩ := primedCreationTriangle_realizedFrontier w h hfin hb j
  have hc := kmswInfFaceSucc_stageTriangle_cycle u hf j
  refine ⟨j, F, hd, hc, ?_, hF⟩
  intro e
  have hd' : d = (stageTriangleDartTriple u j).1 ∨
      d = (stageTriangleDartTriple u j).2.1 ∨
      d = (stageTriangleDartTriple u j).2.2 := by
    simpa only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] using hd
  simpa only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] using
    cycle3_sameCycle_iff _ _ _ _ hc d e hd'

/- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
the three corrected dart images must border the same bounded face on their left.
An edge-multiset image does not supply this oriented statement. -/
@[expose] def primedCreationTriangle_orientedBordersGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : Prop :=
  let u := primedCode (primedSimInput w) h
  let H := primedGeometricDartEquiv w h hfin hb
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  ∀ j : TriangleCreationTime u, ∃ F : PlaneFaces Q,
    ∀ d ∈ stageTriangleDartList u j, Q.dartBorders (H d) F.val

/- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
complementary component beyond the realized primed creation triangles. -/
@[expose] def primedBoundedFaceTriangleCoverageGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : Prop :=
  let u := primedCode (primedSimInput w) h
  let H := primedGeometricDartEquiv w h hfin hb
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  ∀ F : PlaneFaces Q, ∃ j : TriangleCreationTime u,
    frontier F.val.val = ⋃ d ∈ stageTriangleDartList u j, (Q.arc (H d)).image

/- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
is the east dart of the geometric C18 root. No sign assumption is introduced. -/
@[expose] def primedExternalOrbitBordersGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : Prop :=
  let f := kmswInfFaceSucc (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin)
  let H := primedGeometricDartEquiv w h hfin hb
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  ∃ U : Q.Face, Q.IsUnbounded U ∧
    (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
    ∀ d, Q.dartBorders (H d) U ↔ f.SameCycle futureMapOuterDart d

/- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The geometric edges, including the C18 root, remain in the drawing. -/
@[expose] def primedExternalOrbitMissingGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : Prop :=
  let f := kmswInfFaceSucc (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin)
  let H := primedGeometricDartEquiv w h hfin hb
  ∀ d, f.SameCycle futureMapOuterDart d → primeMissingEdge w hfin hb (H d).val.1

end DirectedDistances.KMSW
