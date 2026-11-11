/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.PrimedRealizedFacesClose
public import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsFull
import DirectedDistances.KMSW.PrimedDeletedGeometryEscape
import DirectedDistances.PlanarMap.FiniteDrawingExterior
import DirectedDistances.KMSW.LocalFinitenessIID
import DirectedDistances.KMSW.ShiftedHatCodes
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Connected.LocallyConnected

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! # Primed compressed face orbits

Helpers toward the primed half of Lemma 5.13 (`lem-quad-kmsw`).
The initial root is geometric, missing and unoriented. Statements that use
bounded-face deletion exclusion name the hypothesis `hex` explicitly.

Finite compressed orbits and bounded realized faces are identified below.
The total face equivalence and rooted-map package still require the exterior
component identification, which is not assumed or asserted in this module. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology



@[expose] def primedFaceSetoid (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) : Setoid (ℕ × Bool) where
  r := (kmswInfFaceSucc (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin)).SameCycle
  iseqv := ⟨Equiv.Perm.SameCycle.refl _, Equiv.Perm.SameCycle.symm,
    Equiv.Perm.SameCycle.trans⟩



@[expose] def PrimedFaceOrbit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) := Quotient (primedFaceSetoid w h hfin)



theorem primedFaceOrbit_mk_eq_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (d e : ℕ × Bool) :
    (Quotient.mk (primedFaceSetoid w h hfin) d : PrimedFaceOrbit w h hfin) =
        Quotient.mk _ e ↔
      (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)).SameCycle d e :=
  Quotient.eq



private theorem primedOrbit_cycle3_iff {D : Type*} (f : Equiv.Perm D)
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



private theorem primedOrbit_creation_new_mem (u : ℕ → Fin 3)
    (j : TriangleCreationTime u) :
    ((kmswStage u j.val).nextEdge, true) ∈ stageTriangleDartList u j := by
  by_cases h0 : u j.val = 0
  · cases hl : (kmswStage u j.val).UL.dropLast.reverse <;>
      simp [stageTriangleDartList, stageTriangleDartTriple, h0, hl]
  · simp [stageTriangleDartList, stageTriangleDartTriple, h0]



private theorem primedOrbit_creation_time_le (u : ℕ → Fin 3)
    (j k : TriangleCreationTime u)
    (hsub : ∀ d ∈ stageTriangleDartList u j,
      ∃ e ∈ stageTriangleDartList u k, e.1 = d.1) : j.val ≤ k.val := by
  by_contra hn
  have hkj : k.val + 1 ≤ j.val := by omega
  obtain ⟨e, he, heq⟩ := hsub _ (primedOrbit_creation_new_mem u j)
  have he' := stageTriangleDartList_lt u (k.val + 1) k (by omega) e he
  have hm := kmswStage_nextEdge_mono u hkj
  rw [heq] at he'
  omega



private theorem primedOrbit_creation_eq_of_edges (u : ℕ → Fin 3)
    (j k : TriangleCreationTime u)
    (hj : ∀ d ∈ stageTriangleDartList u j,
      ∃ e ∈ stageTriangleDartList u k, e.1 = d.1)
    (hk : ∀ d ∈ stageTriangleDartList u k,
      ∃ e ∈ stageTriangleDartList u j, e.1 = d.1) : j = k :=
  Subtype.ext (Nat.le_antisymm (primedOrbit_creation_time_le u j k hj)
    (primedOrbit_creation_time_le u k j hk))



private theorem primedOrbit_edge_mem_record (u : ℕ → Fin 3)
    (j : TriangleCreationTime u) (e : ℕ) :
    e ∈ ({(stageTriangleRecord u j).1, (stageTriangleRecord u j).2.1,
      (stageTriangleRecord u j).2.2} : Multiset ℕ) ↔
      ∃ d ∈ stageTriangleDartList u j, d.1 = e := by
  rw [← stageTriangleDartTriple_edges_eq_record]
  simp [stageTriangleDartList, eq_comm]



private theorem primedOrbit_cycle_eq_creation (u : ℕ → Fin 3)
    (hf : primedLimitFiniteIncidence u) (a b c : ℕ × Bool)
    (hc : FaceSucc3Cycle (kmswInfFaceSucc u hf) a b c)
    (j : TriangleCreationTime u)
    (he : ({a.1, b.1, c.1} : Multiset ℕ) =
      {(stageTriangleRecord u j).1, (stageTriangleRecord u j).2.1,
        (stageTriangleRecord u j).2.2}) :
    ∀ d, d ∈ stageTriangleDartList u j ↔ d = a ∨ d = b ∨ d = c := by
  let f := kmswInfFaceSucc u hf
  have hcy (d) : f.SameCycle a d ↔ d = a ∨ d = b ∨ d = c :=
    primedOrbit_cycle3_iff f a b c hc a d (Or.inl rfl)
  have hfinite : {d | f.SameCycle a d}.Finite := by
    apply (Set.toFinite ({a, b, c} : Set (ℕ × Bool))).subset
    intro d hd
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hcy d).mp hd
  obtain ⟨k, hk⟩ := primedRealizedFaces_finiteOrbit_triangle u hf a hfinite
  have hkc := kmswInfFaceSucc_stageTriangle_cycle u hf k
  have hka : a = (stageTriangleDartTriple u k).1 ∨
      a = (stageTriangleDartTriple u k).2.1 ∨
      a = (stageTriangleDartTriple u k).2.2 := by
    simpa only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] using hk
  have hmem (d) : d ∈ stageTriangleDartList u k ↔ d = a ∨ d = b ∨ d = c := by
    have hh := primedOrbit_cycle3_iff f _ _ _ hkc a d hka
    simpa only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false]
      using hh.symm.trans (hcy d)
  have heq : j = k := by
    apply primedOrbit_creation_eq_of_edges u j k
    · intro d hd
      have hids := (primedOrbit_edge_mem_record u j d.1).mpr ⟨d, hd, rfl⟩
      rw [← he] at hids
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hids
      rcases hids with ha | hb | hc
      · exact ⟨a, (hmem a).mpr (Or.inl rfl), ha.symm⟩
      · exact ⟨b, (hmem b).mpr (Or.inr (Or.inl rfl)), hb.symm⟩
      · exact ⟨c, (hmem c).mpr (Or.inr (Or.inr rfl)), hc.symm⟩
    · intro d hd
      apply (primedOrbit_edge_mem_record u j d.1).mp
      rw [← he]
      rcases (hmem d).mp hd with rfl | rfl | rfl <;> simp
  rw [heq]
  exact hmem



private theorem primedOrbit_step (w : ℕ → Fin 3) (h : HasFlowLineHits w)
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



private theorem primedOrbit_oriented_image_of_record (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (j : TriangleCreationTime (primedCode (primedSimInput w) h))
    (J : TriangleCreationTime w)
    (hset : ({primedLimitEdgeMap w h (stageTriangleRecord _ j).1,
      primedLimitEdgeMap w h (stageTriangleRecord _ j).2.1,
      primedLimitEdgeMap w h (stageTriangleRecord _ j).2.2} : Multiset ℕ) =
      {(stageTriangleRecord w J).1, (stageTriangleRecord w J).2.1,
        (stageTriangleRecord w J).2.2}) :
    ∀ d ∈ stageTriangleDartList _ j,
      (primedGeometricDartEquiv w h hfin hb d).val ∈ stageTriangleDartList w J := by
  let u := primedCode (primedSimInput w) h
  let H := primedGeometricDartEquiv w h hfin hb
  have hret : ∀ d ∈ stageTriangleDartList w J, primeGeomEdge w hfin hb d.1 := by
    intro d hd
    have hm := (primedOrbit_edge_mem_record w J d.1).mpr ⟨d, hd, rfl⟩
    rw [← hset] at hm
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
    rcases hm with he | he | he <;>
      exact (primeGeomEdge_iff_primedLimitEdge w hfin hb h _).mpr ⟨_, he.symm⟩
  let T := stageTriangleDartTriple w J
  have ha : T.1 ∈ stageTriangleDartList w J := by simp [T, stageTriangleDartList]
  have hb' : T.2.1 ∈ stageTriangleDartList w J := by simp [T, stageTriangleDartList]
  have hc' : T.2.2 ∈ stageTriangleDartList w J := by simp [T, stageTriangleDartList]
  let x : {d // d ∈ primeDartSet w hfin hb} := ⟨T.1, hret _ ha⟩
  let y : {d // d ∈ primeDartSet w hfin hb} := ⟨T.2.1, hret _ hb'⟩
  let z : {d // d ∈ primeDartSet w hfin hb} := ⟨T.2.2, hret _ hc'⟩
  obtain ⟨hxy, hyz, hzx, hnxy, hnyz, hnzx⟩ :=
    kmswInfFaceSucc_stageTriangle_cycle w hfin J
  have hcycle : FaceSucc3Cycle (kmswInfFaceSucc u (primedCode_finiteIncidence w h hfin))
      (H.symm x) (H.symm y) (H.symm z) := by
    refine ⟨primedOrbit_step w h hfin hb x y hxy,
      primedOrbit_step w h hfin hb y z hyz,
      primedOrbit_step w h hfin hb z x hzx, ?_, ?_, ?_⟩
    · intro he; exact hnxy (congrArg Subtype.val (H.symm.injective he))
    · intro he; exact hnyz (congrArg Subtype.val (H.symm.injective he))
    · intro he; exact hnzx (congrArg Subtype.val (H.symm.injective he))
  have hx : primedLimitEdgeMap w h (H.symm x).1 = T.1.1 :=
    congrArg (fun d => d.val.1) (H.apply_symm_apply x)
  have hy : primedLimitEdgeMap w h (H.symm y).1 = T.2.1.1 :=
    congrArg (fun d => d.val.1) (H.apply_symm_apply y)
  have hz : primedLimitEdgeMap w h (H.symm z).1 = T.2.2.1 :=
    congrArg (fun d => d.val.1) (H.apply_symm_apply z)
  have he : ({(H.symm x).1, (H.symm y).1, (H.symm z).1} : Multiset ℕ) =
      {(stageTriangleRecord u j).1, (stageTriangleRecord u j).2.1,
        (stageTriangleRecord u j).2.2} := by
    apply Multiset.map_injective (primedLimitEdgeMap_injective w h)
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    rw [hx, hy, hz]
    exact (stageTriangleDartTriple_edges_eq_record w J).trans hset.symm
  have hmem := primedOrbit_cycle_eq_creation u (primedCode_finiteIncidence w h hfin)
    (H.symm x) (H.symm y) (H.symm z) hcycle j he
  intro d hd
  rcases (hmem d).mp hd with rfl | rfl | rfl
  · rw [H.apply_symm_apply]; exact ha
  · rw [H.apply_symm_apply]; exact hb'
  · rw [H.apply_symm_apply]; exact hc'




theorem primedCreationTriangle_orientedImageGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedCreationTriangle_orientedImageGoal w h hfin hb := by
  intro j
  obtain ⟨J, hset, _⟩ := primedCreationTriangle_ambientCap w h hfin hb j
  exact ⟨J, primedOrbit_oriented_image_of_record w h hfin hb j J hset⟩



theorem primedCreationTriangle_orientedBordersGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedCreationTriangle_orientedBordersGoal w h hfin hb :=
  primedCreationTriangle_orientedImageGoal_implies_orientedBorders w h hfin hb
    (primedCreationTriangle_orientedImageGoal_holds w h hfin hb)



theorem primedCreationTriangle_border_iff (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (j : TriangleCreationTime (primedCode (primedSimInput w) h)) :
    ∃ F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w)), ∀ d,
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb d) F.val ↔
      d ∈ stageTriangleDartList _ j := by
  classical
  let u := primedCode (primedSimInput w) h
  let H := primedGeometricDartEquiv w h hfin hb
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨J, hset, i, hi, F, hF, hborders⟩ := primedCreationTriangle_ambientCap w h hfin hb j
  have himage := primedOrbit_oriented_image_of_record w h hfin hb j J hset
  let l := (stageTriangleDartList u j).map (fun d => (H d).val)
  have hnd : l.Nodup := (stageTriangleDartList_nodup u j).map
    (Subtype.val_injective.comp H.injective)
  have hsub : l.toFinset ⊆ (stageTriangleDartList w J).toFinset := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact List.mem_toFinset.mpr (himage a ha)
  have heq : l.toFinset = (stageTriangleDartList w J).toFinset := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [List.toFinset_card_of_nodup hnd,
      List.toFinset_card_of_nodup (stageTriangleDartList_nodup w J)]
    simp only [l, List.length_map, stageTriangleDartList, List.length_cons,
      List.length_nil, Nat.le_refl]
  have hcap : (capFace w hfin J).val = F.val.val := by
    let k := (stageTriangleRecord_fin_index w J).choose
    have hk := (stageTriangleRecord_fin_index w J).choose_spec
    exact (capFace_spec w hfin J).1.trans
      ((monotone_cap_region_eq w
        (familyG w (monotone_family_all w) (J.val + 1))
        (familyG w (monotone_family_all w) (J.val + 1)) k i
        (hk.trans hi.symm) (fun _ _ => rfl)).trans hF.symm)
  refine ⟨F, fun d => ⟨?_, fun hd => hborders (H d) (himage d hd)⟩⟩
  intro hd
  have hdP : P.dartBorders (H d).val (capFace w hfin J) :=
    dartBorders_transport Q P F.val (capFace w hfin J) (H d) (H d).val hcap rfl hd
  have hdJ := (cap_border_iff w hfin J (H d).val).mp hdP
  have hdl : (H d).val ∈ l := by
    apply List.mem_toFinset.mp
    rw [heq]
    exact List.mem_toFinset.mpr hdJ
  obtain ⟨a, ha, had⟩ := List.mem_map.mp hdl
  exact H.injective (Subtype.ext had) ▸ ha




theorem primedFiniteFaceOrbit_border_iff (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle d e}.Finite) :
    ∃ F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w)), ∀ e,
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb e) F.val ↔
      (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)).SameCycle d e := by
  let u := primedCode (primedSimInput w) h
  let hf := primedCode_finiteIncidence w h hfin
  obtain ⟨j, _, hd, _, horbit, _⟩ :=
    primedFiniteFaceOrbit_realizedFrontier w h hfin hb d hfinite
  obtain ⟨F, hF⟩ := primedCreationTriangle_border_iff w h hfin hb j
  exact ⟨F, fun e => (hF e).trans (horbit e).symm⟩



private theorem primedOrbit_border_unique {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F G : P.Face) (d : D) (hF : P.dartBorders d F) (hG : P.dartBorders d G) :
    F = G := by
  obtain ⟨a, ha, hF⟩ := hF
  obtain ⟨b, hb, hG⟩ := hG
  let t := min a b / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t < a := by have := min_le_left a b; dsimp [t]; linarith
  have htb : t < b := by have := min_le_right a b; dsimp [t]; linarith
  exact P.faces_eq_of_mem (hF t t ht hta ht hta) (hG t t ht htb ht htb)



private theorem primedOrbit_image_closed (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    IsClosed (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  have heq : Q.image = ⋃ d, (Q.arc d).image := by
    ext z
    constructor
    · rintro (⟨v, rfl⟩ | ⟨d, hd⟩)
      · obtain ⟨d, hd, hv⟩ := v.property
        refine mem_iUnion.mpr ⟨⟨d, hd⟩, ?_⟩
        change P.pos v.val ∈ (P.arc d).image
        rw [← hv, ← P.arc_start]
        exact Or.inl rfl
      · exact mem_iUnion.mpr ⟨d, hd⟩
    · intro hz
      obtain ⟨d, hd⟩ := mem_iUnion.mp hz
      exact Or.inr ⟨d, hd⟩
  have hlocal : LocallyFinite (fun d => (Q.arc d).image) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z (by norm_num), ?_⟩
    apply (Q.locally_finite (Metric.ball z 1) Metric.isBounded_ball).subset
    rintro d ⟨a, ha, hb⟩
    exact ⟨a, hb, ha⟩
  rw [heq]
  exact hlocal.isClosed_iUnion (fun d => (Q.arc d).isCompact_image.isClosed)



private theorem primedOrbit_frontier_subset {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (hclosed : IsClosed P.image) (F : P.Face) : frontier F.val ⊆ P.image := by
  obtain ⟨x, hx, hF⟩ := F.property
  have hopen : IsOpen F.val := by rw [hF]; exact hclosed.isOpen_compl.connectedComponentIn
  intro z hz
  by_contra hzP
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hzP
  obtain ⟨y, hyball, hyF⟩ := (mem_closure_iff.mp hz.1)
    (Metric.ball z ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  have hcomp : connectedComponentIn P.imageᶜ y = F.val := by
    rw [hF] at hyF ⊢
    exact (connectedComponentIn_eq hyF).symm
  have hzF : z ∈ F.val := by
    rw [← hcomp]
    exact (convex_ball z ε).isPreconnected.subset_connectedComponentIn hyball hball
      (Metric.mem_ball_self hε)
  exact hz.2 (hopen.interior_eq.symm ▸ hzF)



private theorem primedOrbit_arc_interior_nonempty {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (d : D) : (P.arc d).interior.Nonempty := by
  let p := P.arc d
  let a := midpoint ℝ p.start (p.point 1)
  let b := midpoint ℝ p.start a
  have hne : p.start ≠ p.point 1 := by
    intro he
    exact P.initial_nonzero d (sub_eq_zero.mpr he.symm)
  have ha : a ≠ p.start := fun he => hne ((midpoint_eq_left_iff ℝ).mp he)
  have hb : b ≠ p.start := by
    intro he
    exact ha ((midpoint_eq_left_iff ℝ).mp he).symm
  have hba : b ≠ a := by
    intro he
    exact ha ((midpoint_eq_right_iff ℝ).mp he).symm
  have ham : a ∈ segment ℝ p.start (p.point 1) := midpoint_mem_segment _ _
  have hbm : b ∈ segment ℝ p.start (p.point 1) :=
    (convex_segment p.start (p.point 1)).segment_subset
      (left_mem_segment ℝ p.start (p.point 1)) ham (midpoint_mem_segment p.start a)
  have himage {z : ℂ} (hz : z ∈ segment ℝ p.start (p.point 1)) : z ∈ p.image := by
    refine Or.inr ⟨0, ?_, ?_⟩
    · have hl := P.arc_length d
      change 2 ≤ p.points.length at hl
      omega
    · change z ∈ segment ℝ (p.point 0) (p.point 1)
      rw [Polyline.point_zero_eq_start]
      exact hz
  by_cases haf : a = p.finish
  · refine ⟨b, himage hbm, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hb, fun he => hba (he.trans haf.symm)⟩
  · refine ⟨a, himage ham, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha, haf⟩




theorem primedBoundedFace_retainedCap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w))) :
    ∃ J : TriangleCreationTime w,
      (capFace w hfin J).val = F.val.val ∧
      ∀ d ∈ stageTriangleDartList w J, primeGeomEdge w hfin hb d.1 := by
  classical
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  obtain ⟨G, hG⟩ :=
    (primedBoundedFace_ambientFaceGoal_iff_deletedGeometryExclusion w hfin hb).mpr hex F
  obtain ⟨J, i, hi, hGi⟩ := primedAmbientBoundedFace_creationCapGoal_holds w h hfin G
  have hFi := hG.symm.trans hGi
  let k := (stageTriangleRecord_fin_index w J).choose
  have hk := (stageTriangleRecord_fin_index w J).choose_spec
  have hcap : (capFace w hfin J).val = F.val.val :=
    (capFace_spec w hfin J).1.trans
      ((monotone_cap_region_eq w
        (familyG w (monotone_family_all w) (J.val + 1))
        (familyG w (monotone_family_all w) (J.val + 1)) k i
        (hk.trans hi.symm) (fun _ _ => rfl)).trans hFi.symm)
  have hfront : frontier
      ((familyG w (monotone_family_all w) (J.val + 1)).cap i).region ⊆ Q.image := by
    rw [← hFi]
    exact primedOrbit_frontier_subset Q (primedOrbit_image_closed w hfin hb) F.val
  refine ⟨J, hcap, ?_⟩
  intro d hd
  have hids := (primedOrbit_edge_mem_record w J d.1).mpr ⟨d, hd, rfl⟩
  have hbound := stageTriangleDartList_lt w (J.val + 1) J (by omega) d hd
  have harc : (P.arc (d.1, false)).image ⊆ Q.image := by
    intro z hz
    apply hfront
    rw [creationCap_frontier_eq_traces w J i hi]
    have htrace : z ∈ stageEdgeTrace
        (familyQ w (monotone_family_all w) (J.val + 1)) d.1 := by
      rw [stageEdgeTrace, dite_eq_left hbound,
        ← familyDrawing_arc w hfin (monotone_family_all w) (J.val + 1)
          (⟨d.1, hbound⟩, false)]
      exact hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hids
    rcases hids with he | he | he
    · exact Or.inl (Or.inl (he ▸ htrace))
    · exact Or.inl (Or.inr (he ▸ htrace))
    · exact Or.inr (he ▸ htrace)
  by_contra hnot
  obtain ⟨z, hz⟩ := primedOrbit_arc_interior_nonempty P (d.1, false)
  exact primedDeletedArc_interior_avoids w hfin hb d.1 hnot hz (harc hz.1)




private theorem primedOrbit_retained_triangle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (J : TriangleCreationTime w)
    (hret : ∀ d ∈ stageTriangleDartList w J, primeGeomEdge w hfin hb d.1) :
    let f := kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)
    let H := primedGeometricDartEquiv w h hfin hb
    ∃ d, {e | f.SameCycle d e}.Finite ∧
      ∀ e, f.SameCycle d e ↔ (H e).val ∈ stageTriangleDartList w J := by
  let f := kmswInfFaceSucc (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin)
  let H := primedGeometricDartEquiv w h hfin hb
  let T := stageTriangleDartTriple w J
  have ha : T.1 ∈ stageTriangleDartList w J := by simp [T, stageTriangleDartList]
  have hb' : T.2.1 ∈ stageTriangleDartList w J := by simp [T, stageTriangleDartList]
  have hc' : T.2.2 ∈ stageTriangleDartList w J := by simp [T, stageTriangleDartList]
  let x : {d // d ∈ primeDartSet w hfin hb} := ⟨T.1, hret _ ha⟩
  let y : {d // d ∈ primeDartSet w hfin hb} := ⟨T.2.1, hret _ hb'⟩
  let z : {d // d ∈ primeDartSet w hfin hb} := ⟨T.2.2, hret _ hc'⟩
  obtain ⟨hxy, hyz, hzx, hnxy, hnyz, hnzx⟩ :=
    kmswInfFaceSucc_stageTriangle_cycle w hfin J
  have hc : FaceSucc3Cycle f (H.symm x) (H.symm y) (H.symm z) := by
    refine ⟨primedOrbit_step w h hfin hb x y hxy,
      primedOrbit_step w h hfin hb y z hyz,
      primedOrbit_step w h hfin hb z x hzx, ?_, ?_, ?_⟩
    · intro he; exact hnxy (congrArg Subtype.val (H.symm.injective he))
    · intro he; exact hnyz (congrArg Subtype.val (H.symm.injective he))
    · intro he; exact hnzx (congrArg Subtype.val (H.symm.injective he))
  have hcy (e) := primedOrbit_cycle3_iff f _ _ _ hc (H.symm x) e (Or.inl rfl)
  refine ⟨H.symm x, ?_, fun e => ?_⟩
  · apply (Set.toFinite ({H.symm x, H.symm y, H.symm z} : Set (ℕ × Bool))).subset
    intro e he
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hcy e).mp he
  · constructor
    · intro he
      rcases (hcy e).mp he with rfl | rfl | rfl
      · rw [H.apply_symm_apply]; exact ha
      · rw [H.apply_symm_apply]; exact hb'
      · rw [H.apply_symm_apply]; exact hc'
    · intro he
      change (H e).val ∈ [T.1, T.2.1, T.2.2] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      apply (hcy e).mpr
      rcases he with he | he | he
      · exact Or.inl (H.injective (by rw [H.apply_symm_apply]; exact Subtype.ext he))
      · exact Or.inr (Or.inl (H.injective (by rw [H.apply_symm_apply]; exact Subtype.ext he)))
      · exact Or.inr (Or.inr (H.injective (by rw [H.apply_symm_apply]; exact Subtype.ext he)))




theorem primedBoundedFace_finiteOrbit_border_iff (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w))) :
    ∃ d, {e | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)).SameCycle d e}.Finite ∧
      ∀ e, (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb e) F.val ↔
        (kmswInfFaceSucc (primedCode (primedSimInput w) h)
          (primedCode_finiteIncidence w h hfin)).SameCycle d e := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  let H := primedGeometricDartEquiv w h hfin hb
  obtain ⟨J, hcap, hret⟩ := primedBoundedFace_retainedCap w h hfin hb hex F
  obtain ⟨d, hd, hcy⟩ := primedOrbit_retained_triangle w h hfin hb J hret
  refine ⟨d, hd, fun e => ?_⟩
  have ht : Q.dartBorders (H e) F.val ↔ P.dartBorders (H e).val (capFace w hfin J) :=
    ⟨dartBorders_transport Q P F.val (capFace w hfin J) (H e) (H e).val hcap rfl,
      dartBorders_transport P Q (capFace w hfin J) F.val (H e).val (H e) hcap.symm rfl⟩
  exact ht.trans ((cap_border_iff w hfin J (H e).val).trans (hcy e).symm)



theorem primedBoundedFace_unique_orbit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w))) :
    ∃! q : PrimedFaceOrbit w h hfin, ∀ e,
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb e) F.val ↔ Quotient.mk _ e = q := by
  obtain ⟨d, _, hd⟩ := primedBoundedFace_finiteOrbit_border_iff w h hfin hb hex F
  have hchar (e) :
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb e) F.val ↔
      Quotient.mk (primedFaceSetoid w h hfin) e = Quotient.mk _ d := by
    rw [primedFaceOrbit_mk_eq_iff]
    exact (hd e).trans ⟨Equiv.Perm.SameCycle.symm, Equiv.Perm.SameCycle.symm⟩
  refine ⟨Quotient.mk _ d, hchar, ?_⟩
  intro q hq
  exact ((hq d).mp ((hd d).mpr (Equiv.Perm.SameCycle.refl _ _))).symm



theorem primedFiniteFaceOrbit_unique_face (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle d e}.Finite) :
    ∃! F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face, ∀ e,
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb e) F ↔
      (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)).SameCycle d e := by
  obtain ⟨F, hF⟩ := primedFiniteFaceOrbit_border_iff w h hfin hb d hfinite
  refine ⟨F.val, hF, ?_⟩
  intro G hG
  exact primedOrbit_border_unique _ G F.val (primedGeometricDartEquiv w h hfin hb d)
    ((hG d).mpr (Equiv.Perm.SameCycle.refl _ _))
    ((hF d).mpr (Equiv.Perm.SameCycle.refl _ _))




theorem primedDart_borders_unique (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) :
    ∃! F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face,
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb d) F := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  let H := primedGeometricDartEquiv w h hfin hb
  have hsub : Q.image ⊆ P.image := mhatPrimeDrawing_image_subset w hfin hb (monotone_family_all w)
  obtain ⟨F, hdF⟩ := dart_borders_exists w hfin hb (H d).val
  obtain ⟨z, hz, hF⟩ := F.property
  have hzQ : z ∉ Q.image := fun hzQ => hz (hsub hzQ)
  let G : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
  have hFG : F.val ⊆ G.val := by
    rw [hF]
    exact connectedComponentIn_mono z (compl_subset_compl.mpr hsub)
  have hdG : Q.dartBorders (H d) G := by
    obtain ⟨δ, hδ, hw⟩ := hdF
    exact ⟨δ, hδ, fun t ε ht htδ hε hεδ => hFG (hw t ε ht htδ hε hεδ)⟩
  exact ⟨G, hdG, fun U hdU => primedOrbit_border_unique Q U G (H d) hdU hdG⟩



@[expose] noncomputable def primedDartFace (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face :=
  (primedDart_borders_unique w h hfin hb d).exists.choose



theorem primedDartFace_eq_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) (F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face) :
    primedDartFace w h hfin hb d = F ↔
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb d) F := by
  have hd : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
      (primedGeometricDartEquiv w h hfin hb d) (primedDartFace w h hfin hb d) :=
    (primedDart_borders_unique w h hfin hb d).exists.choose_spec
  exact ⟨fun he => he ▸ hd,
    fun hF => primedOrbit_border_unique _ _ F (primedGeometricDartEquiv w h hfin hb d) hd hF⟩



theorem primedDartFace_bounded_of_finite (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle d e}.Finite) :
    Bornology.IsBounded (primedDartFace w h hfin hb d).val := by
  obtain ⟨F, hF⟩ := primedFiniteFaceOrbit_border_iff w h hfin hb d hfinite
  have heq := (primedDartFace_eq_iff w h hfin hb d F.val).mpr
    ((hF d).mpr (Equiv.Perm.SameCycle.refl _ _))
  rw [heq]
  exact F.property



theorem primedDartFace_bounded_iff_finite (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (d : ℕ × Bool) :
    Bornology.IsBounded (primedDartFace w h hfin hb d).val ↔
      {e | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)).SameCycle d e}.Finite := by
  constructor
  · intro hd
    obtain ⟨a, ha, hborders⟩ := primedBoundedFace_finiteOrbit_border_iff w h hfin hb hex
      ⟨primedDartFace w h hfin hb d, hd⟩
    have had := (hborders d).mp ((primedDartFace_eq_iff w h hfin hb d _).mp rfl)
    apply ha.subset
    intro e he
    exact had.trans he
  · exact primedDartFace_bounded_of_finite w h hfin hb d



theorem primedRootFaceOrbit_infinite (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) :
    {e | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart e}.Infinite := by
  intro hfinite
  obtain ⟨j, hj⟩ := primedRealizedFaces_finiteOrbit_triangle
    (primedCode (primedSimInput w) h) (primedCode_finiteIncidence w h hfin)
    futureMapOuterDart hfinite
  exact stageTriangleDart_not_limitExternal _ j futureMapOuterDart hj
    (futureMapOuterDart_external _)




theorem primedRootFaceOrbit_border_unbounded (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (d : ℕ × Bool)
    (hd : (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d) :
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded
      (primedDartFace w h hfin hb d) := by
  by_contra hunbounded
  change ¬ ∀ R : ℝ, ∃ z ∈ (primedDartFace w h hfin hb d).val, R < ‖z‖ at hunbounded
  push Not at hunbounded
  obtain ⟨R, hR⟩ := hunbounded
  have hbdd : Bornology.IsBounded (primedDartFace w h hfin hb d).val := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
    exact ⟨R, fun z hz => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hR z hz⟩
  have hfinite := (primedDartFace_bounded_iff_finite w h hfin hb hex d).mp hbdd
  apply primedRootFaceOrbit_infinite w h hfin
  apply hfinite.subset
  intro e he
  exact hd.symm.trans he





theorem iidCodes_ae_primedFiniteFaceOrbit_identification :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w),
        primedCreationTriangle_orientedImageGoal w h hfin hb ∧
        primedCreationTriangle_orientedBordersGoal w h hfin hb ∧
        ∀ d : ℕ × Bool,
          {e | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
            (primedCode_finiteIncidence w h hfin)).SameCycle d e}.Finite →
          ∃ F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w)), ∀ e,
            (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
              (primedGeometricDartEquiv w h hfin hb e) F.val ↔
            (kmswInfFaceSucc (primedCode (primedSimInput w) h)
              (primedCode_finiteIncidence w h hfin)).SameCycle d e := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses]
    with ω hflow hfin hb
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa only [Nat.zero_add] using hflow 0
  exact ⟨h, hfin, hb, primedCreationTriangle_orientedImageGoal_holds _ h hfin hb,
    primedCreationTriangle_orientedBordersGoal_holds _ h hfin hb,
    primedFiniteFaceOrbit_border_iff _ h hfin hb⟩




theorem primedRetainedAmbientCap_preimageGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primedRetainedAmbientCap_preimageGoal w h hfin hb := by
  classical
  intro J hret
  let u := primedCode (primedSimInput w) h
  let H := primedGeometricDartEquiv w h hfin hb
  obtain ⟨d, hfinite, hcy⟩ := primedOrbit_retained_triangle w h hfin hb J hret
  obtain ⟨j, _, _, _, horbit, _⟩ :=
    primedFiniteFaceOrbit_realizedFrontier w h hfin hb d hfinite
  let l := (stageTriangleDartList u j).map (fun e => (H e).val)
  have hnd : l.Nodup := (stageTriangleDartList_nodup u j).map
    (Subtype.val_injective.comp H.injective)
  have hmem (a : ℕ × Bool) : a ∈ l ↔ a ∈ stageTriangleDartList w J := by
    constructor
    · intro ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact (hcy e).mp ((horbit e).mpr he)
    · intro ha
      let x : {d // d ∈ primeDartSet w hfin hb} := ⟨a, hret a ha⟩
      have hx : (H (H.symm x)).val = a := congrArg Subtype.val (H.apply_symm_apply x)
      apply List.mem_map.mpr
      refine ⟨H.symm x, (horbit _).mp ((hcy _).mpr ?_), hx⟩
      rw [hx]
      exact ha
  have hperm : l.Perm (stageTriangleDartList w J) :=
    (List.perm_ext_iff_of_nodup hnd (stageTriangleDartList_nodup w J)).mpr hmem
  have heq : (↑(l.map Prod.fst) : Multiset ℕ) =
      ↑((stageTriangleDartList w J).map Prod.fst) := Quot.sound (hperm.map Prod.fst)
  change ({primedLimitEdgeMap w h (stageTriangleDartTriple u j).1.1,
      primedLimitEdgeMap w h (stageTriangleDartTriple u j).2.1.1,
      primedLimitEdgeMap w h (stageTriangleDartTriple u j).2.2.1} : Multiset ℕ) =
      {(stageTriangleDartTriple w J).1.1, (stageTriangleDartTriple w J).2.1.1,
        (stageTriangleDartTriple w J).2.2.1} at heq
  have hmap := congrArg (Multiset.map (primedLimitEdgeMap w h))
    (stageTriangleDartTriple_edges_eq_record u j)
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at hmap
  exact ⟨j, hmap.symm.trans (heq.trans (stageTriangleDartTriple_edges_eq_record w J))⟩




theorem primedDartFace_eq_of_finite_sameCycle (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (d e : ℕ × Bool)
    (hfinite : {a | (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle d a}.Finite)
    (hde : (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle d e) :
    primedDartFace w h hfin hb d = primedDartFace w h hfin hb e := by
  obtain ⟨F, hF⟩ := primedFiniteFaceOrbit_border_iff w h hfin hb d hfinite
  exact ((primedDartFace_eq_iff w h hfin hb d F.val).mpr
    ((hF d).mpr (Equiv.Perm.SameCycle.refl _ _))).trans
      ((primedDartFace_eq_iff w h hfin hb e F.val).mpr ((hF e).mpr hde)).symm

end DirectedDistances.KMSW
