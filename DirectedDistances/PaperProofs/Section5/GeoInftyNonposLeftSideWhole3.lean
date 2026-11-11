/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole2

 

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: a triangular face cycle has exactly its three darts. -/
private theorem primedFaceOrbit_cycle3_iff {D : Type*} (f : Equiv.Perm D)
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

/-- Helper toward Lemma 5.5: record edges are exactly creation-triangle darts. -/
private theorem primedFaceOrbit_edge_mem_record (u : ℕ → Fin 3)
    (j : TriangleCreationTime u) (e : ℕ) :
    e ∈ ({(stageTriangleRecord u j).1, (stageTriangleRecord u j).2.1,
      (stageTriangleRecord u j).2.2} : Multiset ℕ) ↔
      ∃ d ∈ stageTriangleDartList u j, d.1 = e := by
  rw [← stageTriangleDartTriple_edges_eq_record]
  simp [stageTriangleDartList, eq_comm]

/-- Helper toward Lemma 5.5: the new edge belongs to its creation triangle. -/
private theorem primedFaceOrbit_creation_new_mem (u : ℕ → Fin 3)
    (j : TriangleCreationTime u) :
    ((kmswStage u j.val).nextEdge, true) ∈ stageTriangleDartList u j := by
  by_cases h0 : u j.val = 0
  · cases hl : (kmswStage u j.val).UL.dropLast.reverse <;>
      simp [stageTriangleDartList, stageTriangleDartTriple, h0, hl]
  · simp [stageTriangleDartList, stageTriangleDartTriple, h0]

/-- Helper toward Lemma 5.5: edge containment orders creation times. -/
private theorem primedFaceOrbit_creation_time_le (u : ℕ → Fin 3)
    (j k : TriangleCreationTime u)
    (hsub : ∀ d ∈ stageTriangleDartList u j,
      ∃ e ∈ stageTriangleDartList u k, e.1 = d.1) : j.val ≤ k.val := by
  by_contra hn
  have hkj : k.val + 1 ≤ j.val := by omega
  obtain ⟨e, he, heq⟩ := hsub _ (primedFaceOrbit_creation_new_mem u j)
  have he' := stageTriangleDartList_lt u (k.val + 1) k (by omega) e he
  have hm := kmswStage_nextEdge_mono u hkj
  rw [heq] at he'
  omega

/-- Helper toward Lemma 5.5: the creation time is determined by its edge set. -/
private theorem primedFaceOrbit_creation_eq_of_edges (u : ℕ → Fin 3)
    (j k : TriangleCreationTime u)
    (hj : ∀ d ∈ stageTriangleDartList u j,
      ∃ e ∈ stageTriangleDartList u k, e.1 = d.1)
    (hk : ∀ d ∈ stageTriangleDartList u k,
      ∃ e ∈ stageTriangleDartList u j, e.1 = d.1) : j = k :=
  Subtype.ext (Nat.le_antisymm (primedFaceOrbit_creation_time_le u j k hj)
    (primedFaceOrbit_creation_time_le u k j hk))

/-- Helper toward Lemma 5.5: a three-cycle determines its creation triangle. -/
private theorem primedFaceOrbit_cycle_eq_creation (u : ℕ → Fin 3)
    (hf : primedLimitFiniteIncidence u) (a b c : ℕ × Bool)
    (hc : FaceSucc3Cycle (kmswInfFaceSucc u hf) a b c)
    (j : TriangleCreationTime u)
    (he : ({a.1, b.1, c.1} : Multiset ℕ) =
      {(stageTriangleRecord u j).1, (stageTriangleRecord u j).2.1,
        (stageTriangleRecord u j).2.2}) :
    ∀ d, d ∈ stageTriangleDartList u j ↔ d = a ∨ d = b ∨ d = c := by
  let f := kmswInfFaceSucc u hf
  have hcy (d) : f.SameCycle a d ↔ d = a ∨ d = b ∨ d = c :=
    primedFaceOrbit_cycle3_iff f a b c hc a d (Or.inl rfl)
  have hfinite : {d | f.SameCycle a d}.Finite := by
    apply (Set.toFinite ({a, b, c} : Set (ℕ × Bool))).subset
    intro d hd
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hcy d).mp hd
  obtain ⟨k, hk⟩ := primedRealizedFaces_finiteOrbit_triangle u hf a hfinite
  have hkc := kmswInfFaceSucc_stageTriangle_cycle u hf k
  have hka : a = (stageTriangleDartTriple u k).1 ∨
      a = (stageTriangleDartTriple u k).2.1 ∨ a = (stageTriangleDartTriple u k).2.2 := by
    simpa only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] using hk
  have hmem (d) : d ∈ stageTriangleDartList u k ↔ d = a ∨ d = b ∨ d = c := by
    have hh := primedFaceOrbit_cycle3_iff f _ _ _ hkc a d hka
    simpa only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false]
      using hh.symm.trans (hcy d)
  have heq : j = k := by
    apply primedFaceOrbit_creation_eq_of_edges u j k
    · intro d hd
      have hids := (primedFaceOrbit_edge_mem_record u j d.1).mpr ⟨d, hd, rfl⟩
      rw [← he] at hids
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hids
      rcases hids with ha | hb | hc
      · exact ⟨a, (hmem a).mpr (Or.inl rfl), ha.symm⟩
      · exact ⟨b, (hmem b).mpr (Or.inr (Or.inl rfl)), hb.symm⟩
      · exact ⟨c, (hmem c).mpr (Or.inr (Or.inr rfl)), hc.symm⟩
    · intro d hd
      apply (primedFaceOrbit_edge_mem_record u j d.1).mp
      rw [← he]
      rcases (hmem d).mp hd with rfl | rfl | rfl <;> simp
  rw [heq]
  exact hmem

/-- Helper toward Lemma 5.5: primed successors agree with ambient triangle steps. -/
private theorem primedFaceOrbit_step (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
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

/-- Helper toward Lemma 5.5: a primed creation cap preserves its face step. -/
private theorem lMinusPrimedImage_future_faceSucc
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (j : TriangleCreationTime
      (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)) :
    ∃ J : TriangleCreationTime (boundaryGluingFutureStream W h k),
      ({primedLimitEdgeMap (boundaryGluingFutureStream W h k) hτ
          (stageTriangleRecord _ j).1,
        primedLimitEdgeMap (boundaryGluingFutureStream W h k) hτ
          (stageTriangleRecord _ j).2.1,
        primedLimitEdgeMap (boundaryGluingFutureStream W h k) hτ
          (stageTriangleRecord _ j).2.2} : Multiset ℕ) =
        {(stageTriangleRecord _ J).1, (stageTriangleRecord _ J).2.1,
          (stageTriangleRecord _ J).2.2} ∧
      (∀ d ∈ stageTriangleDartList
          (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) j,
        (primedGeometricDartEquiv (boundaryGluingFutureStream W h k) hτ
          (show primedLimitFiniteIncidence (boundaryGluingFutureStream W h k) by
            simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin)
          (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) d).val ∈
            stageTriangleDartList (boundaryGluingFutureStream W h k) J) ∧
      (∀ d ∈ stageTriangleDartList
          (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) j,
        (primedGeometricDartEquiv (boundaryGluingFutureStream W h k) hτ
          (show primedLimitFiniteIncidence (boundaryGluingFutureStream W h k) by
            simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin)
          (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ)
          (kmswInfFaceSucc
            (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
            (primedCode_finiteIncidence (boundaryGluingFutureStream W h k) hτ hfin) d)).val =
        kmswInfFaceSucc (boundaryGluingFutureStream W h k)
          (show KMSWFiniteIncidence (boundaryGluingFutureStream W h k) by
            simpa only [KMSWFiniteIncidence, hatLimitFiniteIncidence] using hfin)
          (primedGeometricDartEquiv (boundaryGluingFutureStream W h k) hτ
            (show primedLimitFiniteIncidence (boundaryGluingFutureStream W h k) by
              simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin)
            (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) d).val) := by
  let U := boundaryGluingFutureStream W h k
  let hf : KMSWFiniteIncidence U := by
    simpa only [KMSWFiniteIncidence, hatLimitFiniteIncidence] using hfin
  let hb := hatBoundaryHitWitnesses U hτ
  let H := primedGeometricDartEquiv U hτ
    (show primedLimitFiniteIncidence U by
      simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin) hb
  obtain ⟨J, hset, _, _, _⟩ := primedCreationTriangle_ambientCap U hτ
    (show primedLimitFiniteIncidence U by
      simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin) hb j
  have hret : ∀ d ∈ stageTriangleDartList U J, primeGeomEdge U hf hb d.1 := by
    intro d hd
    have hm := (primedFaceOrbit_edge_mem_record U J d.1).mpr ⟨d, hd, rfl⟩
    rw [← hset] at hm
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
    rcases hm with he | he | he <;>
      exact (primeGeomEdge_iff_primedLimitEdge U hf hb hτ _).mpr ⟨_, he.symm⟩
  let T := stageTriangleDartTriple U J
  have ha : T.1 ∈ stageTriangleDartList U J := by simp [T, stageTriangleDartList]
  have hb' : T.2.1 ∈ stageTriangleDartList U J := by simp [T, stageTriangleDartList]
  have hc' : T.2.2 ∈ stageTriangleDartList U J := by simp [T, stageTriangleDartList]
  let x : {d // d ∈ primeDartSet U hf hb} := ⟨T.1, hret _ ha⟩
  let y : {d // d ∈ primeDartSet U hf hb} := ⟨T.2.1, hret _ hb'⟩
  let z : {d // d ∈ primeDartSet U hf hb} := ⟨T.2.2, hret _ hc'⟩
  obtain ⟨hxy, hyz, hzx, hnxy, hnyz, hnzx⟩ := kmswInfFaceSucc_stageTriangle_cycle U hf J
  have hcycle : FaceSucc3Cycle
      (kmswInfFaceSucc (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin)) (H.symm x) (H.symm y) (H.symm z) := by
    refine ⟨primedFaceOrbit_step U hτ hf hb x y hxy,
      primedFaceOrbit_step U hτ hf hb y z hyz,
      primedFaceOrbit_step U hτ hf hb z x hzx, ?_, ?_, ?_⟩
    · intro he; exact hnxy (congrArg Subtype.val (H.symm.injective he))
    · intro he; exact hnyz (congrArg Subtype.val (H.symm.injective he))
    · intro he; exact hnzx (congrArg Subtype.val (H.symm.injective he))
  have hx : primedLimitEdgeMap U hτ (H.symm x).1 = T.1.1 :=
    congrArg (fun d => d.val.1) (H.apply_symm_apply x)
  have hy : primedLimitEdgeMap U hτ (H.symm y).1 = T.2.1.1 :=
    congrArg (fun d => d.val.1) (H.apply_symm_apply y)
  have hz : primedLimitEdgeMap U hτ (H.symm z).1 = T.2.2.1 :=
    congrArg (fun d => d.val.1) (H.apply_symm_apply z)
  have he : ({(H.symm x).1, (H.symm y).1, (H.symm z).1} : Multiset ℕ) =
      {(stageTriangleRecord _ j).1, (stageTriangleRecord _ j).2.1,
        (stageTriangleRecord _ j).2.2} := by
    apply Multiset.map_injective (primedLimitEdgeMap_injective U hτ)
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    rw [hx, hy, hz]
    exact (stageTriangleDartTriple_edges_eq_record U J).trans hset.symm
  have hmem := primedFaceOrbit_cycle_eq_creation _
    (primedCode_finiteIncidence U hτ hfin)
    (H.symm x) (H.symm y) (H.symm z) hcycle j he
  refine ⟨J, hset, ?_, ?_⟩
  · intro d hd
    rcases (hmem d).mp hd with hdx | hdy | hdz
    · subst d; rw [H.apply_symm_apply]; exact ha
    · subst d; rw [H.apply_symm_apply]; exact hb'
    · subst d; rw [H.apply_symm_apply]; exact hc'
  · intro d hd
    rcases (hmem d).mp hd with hdx | hdy | hdz
    · subst d
      rw [primedFaceOrbit_step U hτ hf hb x y hxy]
      rw [H.apply_symm_apply, H.apply_symm_apply]
      exact hxy.symm
    · subst d
      rw [primedFaceOrbit_step U hτ hf hb y z hyz]
      rw [H.apply_symm_apply, H.apply_symm_apply]
      exact hyz.symm
    · subst d
      rw [primedFaceOrbit_step U hτ hf hb z x hzx]
      rw [H.apply_symm_apply, H.apply_symm_apply]
      exact hzx.symm

/-- Helper toward Lemma 5.5: a future window preserves triangle successors. -/
private theorem lMinusWhole_window_faceSucc_of_triangle (w : ℕ → Fin 3) (s : ℕ)
    (hu : KMSWFiniteIncidence (fun i => w (s + i))) (hw : KMSWFiniteIncidence w)
    (d : ℕ × Bool)
    (hd : ∃ j : TriangleCreationTime (fun i => w (s + i)),
      d ∈ stageTriangleDartList (fun i => w (s + i)) j) :
    (kmswWindowEdgeMapInf w s
        (kmswInfFaceSucc (fun i => w (s + i)) hu d).1,
      (kmswInfFaceSucc (fun i => w (s + i)) hu d).2) =
      kmswInfFaceSucc w hw (kmswWindowEdgeMapInf w s d.1, d.2) := by
  let u := fun i => w (s + i)
  obtain ⟨j, hdj⟩ := hd
  obtain ⟨a, ha⟩ := kmswInfFaceSucc_eventually_eq_stage u hu d
  obtain ⟨b, hb⟩ := kmswInfFaceSucc_eventually_eq_stage w hw
    (kmswWindowEdgeMapInf w s d.1, d.2)
  let m := max (max a b) (j.val + 1)
  obtain ⟨hedge, hsrc⟩ := ha m (by dsimp only [m]; omega)
  obtain ⟨himage, htgt⟩ := hb (s + m) (by dsimp only [m]; omega)
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, hedge⟩, d.2)
  have hx : (x.1.val, x.2) ∈ stageTriangleDartsVal u m := by
    apply List.mem_flatMap.mpr
    exact ⟨j, (mem_stageTriangleTimes u m j).mpr (by dsimp only [m]; omega), hdj⟩
  have hface := kmswWindowDartMap_faceSucc w s m x hx
  have hmap : kmswWindowDartMap w s m x =
      (⟨kmswWindowEdgeMapInf w s d.1, himage⟩, d.2) := by
    apply Prod.ext
    · apply Fin.ext
      exact (kmswWindowEdgeMapInf_eq_stage w s m d.1 hedge).symm
    · rfl
  rw [hsrc]
  have hout := kmswWindowEdgeMapInf_eq_stage w s m
    ((kmswMap u m).faceSucc x).1.val ((kmswMap u m).faceSucc x).1.isLt
  change (kmswWindowEdgeMapInf w s ((kmswMap u m).faceSucc x).1.val,
    ((kmswMap u m).faceSucc x).2) = _
  rw [hout]
  change ((kmswWindowDartMap w s m ((kmswMap u m).faceSucc x)).1.val,
    (kmswWindowDartMap w s m ((kmswMap u m).faceSucc x)).2) = _
  rw [← hface, hmap]
  exact htgt.symm

/-- Helper toward Lemma 5.5: a future window embeds each complete triangle. -/
private theorem lMinusWhole_window_triangle_rotated
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (j : TriangleCreationTime (boundaryGluingFutureStream W h k)) :
    List.IsRotated
      ((stageTriangleDartList (boundaryGluingFutureStream W h k) j).map
        (fun d => (boundaryGluingEdgeMap W h k d.1, d.2)))
      (stageTriangleDartList (shiftedStream W 0)
        ⟨boundaryHitTime (shiftedStream W 0) h k + j.val, j.property⟩) := by
  let w := shiftedStream W 0
  let n := boundaryHitTime w h k
  let U := boundaryGluingFutureStream W h k
  have hr := kmswWindowPatchData_triangle_rotated w n (j.val + 1) j.val
    (Nat.lt_succ_self _) j.property
  have hm : (stageTriangleDartList U j).map
      (fun d => (boundaryGluingEdgeMap W h k d.1, d.2)) =
      (stageTriangleDartList U j).map
        (fun d => ((kmswWindowPatchData w n (j.val + 1)).φ d.1, d.2)) := by
    apply List.map_congr_left
    intro d hd
    have hdlt : d.1 < (kmswStage U (j.val + 1)).nextEdge := by
      apply stage_face_dart_lt_nextEdge U (j.val + 1) d
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨j, (mem_stageTriangleTimes U (j.val + 1) j).mpr (Nat.lt_succ_self _), hd⟩))
    exact Prod.ext (kmswWindowEdgeMapInf_eq_stage w n (j.val + 1) d.1 hdlt) rfl
  rw [hm]
  exact hr

/-- Helper toward Lemma 5.5: the corrected primed darts are the window image. -/
private theorem lMinusPrimedDartImage_eq_windowImage
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (d : ℕ × Bool) :
    lMinusPrimedDartImage hτ d =
      (boundaryGluingEdgeMap W h k
        (primedGeometricDartEquiv (boundaryGluingFutureStream W h k) hτ
          (show primedLimitFiniteIncidence (boundaryGluingFutureStream W h k) by
            simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin)
          (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) d).val.1,
        (primedGeometricDartEquiv (boundaryGluingFutureStream W h k) hτ
          (show primedLimitFiniteIncidence (boundaryGluingFutureStream W h k) by
            simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin)
          (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) d).val.2) := by
  simp [lMinusPrimedDartImage, boundaryGluingPrimedEdgeMap, boundaryGluingEdgeMap,
    primedGeometricDartEquiv_apply, primedLimitDartMap]

section PrimedRetention

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "U" => boundaryGluingFutureStream W h k
local notation "p" => primedCode (primedSimInput U) hτ
local notation "hf" => primedCode_finiteIncidence U hτ hfin
local notation "hb" => hatBoundaryHitWitnesses U hτ
include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: each primed creation triangle is retained as a
run-zero creation triangle, with its exact infinite face successor. -/
theorem lMinusPrimedCreationTriangle_retained
    (j : TriangleCreationTime p) :
    ∃ J : TriangleCreationTime (shiftedStream W 0),
      (∀ d ∈ stageTriangleDartList p j,
        lMinusPrimedDartImage hτ d ∈ stageTriangleDartList (shiftedStream W 0) J) ∧
      (∀ d ∈ stageTriangleDartList (shiftedStream W 0) J,
        d.1 ∈ (m0GeodesicSide hp P ThinMapSide.left).edges) ∧
      (∀ d ∈ stageTriangleDartList p j,
        lMinusPrimedDartImage hτ (kmswInfFaceSucc p hf d) =
          kmswInfFaceSucc (shiftedStream W 0) (H.1 0)
            (lMinusPrimedDartImage hτ d)) := by
  let w := shiftedStream W 0
  let n := boundaryHitTime w h k
  obtain ⟨J₀, hset, hstage, hsucc⟩ := lMinusPrimedImage_future_faceSucc hτ hfin j
  let Hp := primedGeometricDartEquiv U hτ
    (show primedLimitFiniteIncidence U by
      simpa only [primedLimitFiniteIncidence, hatLimitFiniteIncidence] using hfin) hb
  let J : TriangleCreationTime w := ⟨n + J₀.val, by
    simpa only [boundaryGluingFutureStream, w, n] using J₀.property⟩
  have hrot := lMinusWhole_window_triangle_rotated W h k J₀
  refine ⟨J, ?_, ?_, ?_⟩
  · intro d hd
    have hmem : (Hp d).val ∈ stageTriangleDartList U J₀ := hstage d hd
    have hmap : (boundaryGluingEdgeMap W h k (Hp d).val.1, (Hp d).val.2) ∈
        (stageTriangleDartList U J₀).map
          (fun e => (boundaryGluingEdgeMap W h k e.1, e.2)) :=
      List.mem_map.mpr ⟨(Hp d).val, hmem, rfl⟩
    have htarget := hrot.mem_iff.mp hmap
    have hJ : J = ⟨n + J₀.val, J₀.property⟩ := rfl
    rw [hJ]
    rw [lMinusPrimedDartImage_eq_windowImage hτ hfin]
    exact htarget
  · intro d hd
    have hmem := hrot.mem_iff.mpr (by
      rw [show J = ⟨n + J₀.val, J₀.property⟩ by rfl] at hd
      exact hd)
    obtain ⟨e, he, hde⟩ := List.mem_map.mp hmem
    have hm : e.1 ∈ ({(stageTriangleRecord U J₀).1,
        (stageTriangleRecord U J₀).2.1, (stageTriangleRecord U J₀).2.2} : Multiset ℕ) :=
      (primedFaceOrbit_edge_mem_record U J₀ e.1).mpr ⟨e, he, rfl⟩
    rw [← hset] at hm
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
    have hsource : ∃ a ∈ stageTriangleDartList p j,
        primedLimitEdgeMap U hτ a.1 = e.1 := by
      rcases hm with h1 | h2 | h3
      · obtain ⟨a, ha, hae⟩ := (primedFaceOrbit_edge_mem_record p j
          (stageTriangleRecord p j).1).mp (by simp)
        exact ⟨a, ha, (congrArg (primedLimitEdgeMap U hτ) hae).trans h1.symm⟩
      · obtain ⟨a, ha, hae⟩ := (primedFaceOrbit_edge_mem_record p j
          (stageTriangleRecord p j).2.1).mp (by simp)
        exact ⟨a, ha, (congrArg (primedLimitEdgeMap U hτ) hae).trans h2.symm⟩
      · obtain ⟨a, ha, hae⟩ := (primedFaceOrbit_edge_mem_record p j
          (stageTriangleRecord p j).2.2).mp (by simp)
        exact ⟨a, ha, (congrArg (primedLimitEdgeMap U hτ) hae).trans h3.symm⟩
    obtain ⟨a, ha, hae⟩ := hsource
    have hside := lMinusPrimedDartImage_mem_leftSide
      hτ hp P hqMode Tpath hfin hleft hk a
    have hedge : (lMinusPrimedDartImage hτ a).1 = d.1 := by
      rw [lMinusPrimedDartImage_eq_windowImage hτ hfin]
      change boundaryGluingEdgeMap W h k
        (primedLimitEdgeMap U hτ a.1) = d.1
      calc
        boundaryGluingEdgeMap W h k (primedLimitEdgeMap U hτ a.1) =
            boundaryGluingEdgeMap W h k e.1 := congrArg _ hae
        _ = d.1 := congrArg Prod.fst hde
    exact hedge ▸ hside
  · intro d hd
    have hmem := hstage d hd
    have hfu : KMSWFiniteIncidence U := by
      simpa only [KMSWFiniteIncidence, hatLimitFiniteIncidence] using hfin
    have hwindow := lMinusWhole_window_faceSucc_of_triangle w n hfu (H.1 0)
      (Hp d).val ⟨J₀, hmem⟩
    calc
      lMinusPrimedDartImage hτ (kmswInfFaceSucc p hf d) =
          (boundaryGluingEdgeMap W h k (Hp (kmswInfFaceSucc p hf d)).val.1,
            (Hp (kmswInfFaceSucc p hf d)).val.2) :=
        lMinusPrimedDartImage_eq_windowImage hτ hfin _
      _ = (boundaryGluingEdgeMap W h k
            (kmswInfFaceSucc U hfu (Hp d).val).1,
            (kmswInfFaceSucc U hfu (Hp d).val).2) :=
        congrArg (fun e : ℕ × Bool => (boundaryGluingEdgeMap W h k e.1, e.2))
          (hsucc d hd)
      _ = kmswInfFaceSucc w (H.1 0)
          (boundaryGluingEdgeMap W h k (Hp d).val.1, (Hp d).val.2) := hwindow
      _ = kmswInfFaceSucc w (H.1 0) (lMinusPrimedDartImage hτ d) := by
        rw [lMinusPrimedDartImage_eq_windowImage hτ hfin]

end PrimedRetention
























end DirectedDistances.PaperProofs.Section5
